// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * tracer.h:
 *   latency tracing functions
 *
 **********************************************************************/

#ifndef _LIB_TRACER_H_
#define _LIB_TRACER_H_

#include <sys/time.h>
#include <map>
#include <string>

/* Trace details of an individual type of request. */
typedef struct Request_Trace
{
    bool is_tracing;
    uint64_t start_time;
    uint8_t curr_stage;
    uint8_t max_stage;
    uint32_t stage[16];
    uint32_t n_traces;
} Request_Trace;

/* Mapping of names to request trace data structure. */
static std::map<std::string, Request_Trace *> trace_map;

void
Trace_Init(const std::string &name, Request_Trace *trace);

void
Trace_Flush(const std::string &name);

void
Trace_Start(const std::string &name);

void
Trace_Save(const std::string &name, const uint32_t index = 0);

void
Trace_Stop(const std::string &name);

#endif // _LIB_TRACER_H_
