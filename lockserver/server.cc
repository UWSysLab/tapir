// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * lockserver/server.cc:
 *   A lockserver replica.
 *
 * Copyright 2015 Naveen Kr. Sharma <naveenks@cs.washington.edu>
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 **********************************************************************/

#include "lockserver/server.h"

#include <algorithm>
#include <iterator>
#include <unordered_set>

namespace lockserver {

using namespace proto;

LockServer::LockServer() { }
LockServer::~LockServer() { }

void
LockServer::ExecInconsistentUpcall(const string &str1)
{
    Debug("ExecInconsistent: %s\n", str1.c_str());

    Request request;

    request.ParseFromString(str1);
    string key = request.key();
    uint64_t client_id = request.clientid();

    if (request.type()) { // Lock operation.
        Warning("Lock operation being sent as Inconsistent. Ignored.");
    } else {
        if (locks.find(key) != locks.end()) {
            if (client_id == locks[key]) {
                Debug("Releasing lock %lu: %s", client_id, key.c_str());
                locks.erase(key);
            } else {
                Debug("Lock held by someone else %lu: %s, %lu",
                        client_id, key.c_str(), locks[key]);
            }
        } else {
            Debug("Lock held by no one.");
        }
    }
}

void
LockServer::ExecConsensusUpcall(const string &str1, string &str2)
{
    Debug("ExecConsensus: %s\n", str1.c_str());

    Request request;
    Reply reply;

    request.ParseFromString(str1);
    string key = request.key();
    uint64_t client_id = request.clientid();
    reply.set_key(key);
    int status = 0;

    if (request.type()) { // Lock operation.
        if (locks.find(key) == locks.end()) {
            Debug("Assigning lock %lu: %s", client_id, key.c_str());
            locks[key] = client_id;
        } else if (locks[key] != client_id) {
            Debug("Lock already held %lu: %s", client_id, key.c_str());
            status = -1;
        }
    } else {
        Warning("Unlock operation being sent as Consensus");
        if (locks.find(key) == locks.end()) {
            Debug("Lock held by no-one %lu: %s", client_id, key.c_str());
            status = -2;
        } else if (locks[key] != client_id) {
            Debug("Lock held by someone else %lu: %s, %lu",
                    client_id, key.c_str(), locks[key]);
            status = -2;
        } else {
            Debug("Releasing lock %lu: %s", client_id, key.c_str());
            locks.erase(key);
        }
    }

    reply.set_status(status);
    reply.SerializeToString(&str2);
}

void
LockServer::UnloggedUpcall(const string &str1, string &str2)
{
    Debug("Unlogged: %s\n", str1.c_str());
}

void
LockServer::Sync(const std::map<opid_t, RecordEntry>& record) {
    locks.clear();

    struct KeyLockInfo {
        std::unordered_set<uint64_t> locked;
        std::unordered_set<uint64_t> unlocked;
    };
    std::unordered_map<std::string, KeyLockInfo> key_lock_info;

    for (const std::pair<const opid_t, RecordEntry> &p : record) {
        const opid_t &opid = p.first;
        const RecordEntry &entry = p.second;

        Request request;
        request.ParseFromString(entry.request.op());
        Reply reply;
        reply.ParseFromString(entry.result);
        KeyLockInfo &info = key_lock_info[request.key()];

        Debug("Sync opid=(%lu, %lu), clientid=%lu, key=%s, type=%d, status=%d.",
              opid.first, opid.second, request.clientid(),
              request.key().c_str(), request.type(), reply.status());

        if (request.type() && reply.status() == 0) {
            // Lock.
            info.locked.insert(request.clientid());
        } else if (!request.type() && reply.status() == 0) {
            // Unlock.
            info.unlocked.insert(request.clientid());
        }
    }

    for (const std::pair<const std::string, KeyLockInfo> &p : key_lock_info) {
        const std::string &key = p.first;
        const KeyLockInfo &info = p.second;
        std::unordered_set<uint64_t> diff;
        std::set_difference(std::begin(info.locked), std::end(info.locked),
                            std::begin(info.unlocked), std::end(info.unlocked),
                            std::inserter(diff, diff.begin()));

        ASSERT(diff.size() == 0 || diff.size() == 1);
        if (diff.size() == 1) {
            uint64_t client_id = *std::begin(diff);
            Debug("Assigning lock %lu: %s", client_id, key.c_str());
            locks[key] = client_id;
        }
    }
}

std::map<opid_t, std::string>
LockServer::Merge(const std::map<opid_t, std::vector<RecordEntry>> &d,
                  const std::map<opid_t, std::vector<RecordEntry>> &u,
                  const std::map<opid_t, std::string> &majority_results_in_d) {
    // First note that d and u only contain consensus operations, and lock
    // requests are the only consensus operations (unlock is an inconsistent
    // operation), so d and u only contain lock requests. To merge, we grant
    // any majority successful lock request in d if it does not conflict with a
    // currently held lock. We do not grant any other lock request.

    std::map<opid_t, std::string> results;

    using EntryVec = std::vector<RecordEntry>;
    for (const std::pair<const opid_t, EntryVec>& p: d) {
        const opid_t &opid = p.first;
        const EntryVec &entries = p.second;

        // Get the request and reply.
        const RecordEntry &entry = *std::begin(entries);

        Request request;
        request.ParseFromString(entry.request.op());

        Reply reply;
        auto iter = majority_results_in_d.find(opid);
        ASSERT(iter != std::end(majority_results_in_d));
        reply.ParseFromString(iter->second);

        // Form the final result.
        const bool operation_successful = reply.status() == 0;
        if (operation_successful) {
            // If the lock was successful, then we acquire the lock so long as
            // it is not already held.
            const std::string &key = reply.key();
            if (locks.count(key) == 0) {
                Debug("Assigning lock %lu: %s", request.clientid(),
                      key.c_str());
                locks[key] = request.clientid();
                results[opid] = iter->second;
            } else {
                Debug("Rejecting lock %lu: %s", request.clientid(),
                      key.c_str());
                reply.set_status(-1);
                std::string s;
                reply.SerializeToString(&s);
                results[opid] = s;
            }
        } else {
            // If the lock was not successful, then we maintain this as the
            // majority result.
            results[opid] = iter->second;
        }
    }

    // We reject all lock requests in u. TODO: We could acquire a lock if
    // it is free, but it's simplest to just reject them unilaterally.
    for (const std::pair<const opid_t, EntryVec>& p: u) {
        const opid_t &opid = p.first;
        const EntryVec &entries = p.second;

        const RecordEntry &entry = *std::begin(entries);
        Request request;
        request.ParseFromString(entry.request.op());

        Debug("Rejecting lock %lu: %s", request.clientid(),
              request.key().c_str());
        Reply reply;
        reply.set_key(request.key());
        reply.set_status(-1);
        std::string s;
        reply.SerializeToString(&s);
        results[opid] = s;
    }

    return results;
}

} // namespace lockserver
