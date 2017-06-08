------------------------ MODULE VR ------------------------------------------
(***************************************************************************)
(* This is a TLA+ specification of the VR algorithm.                       *)
(***************************************************************************)
EXTENDS FiniteSets, Naturals, TLC, TLAPS

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Constants}} ^'                                *)
(***************************************************************************)

(***************************************************************************)
(*  Constant parameters:                                                   *)
(*        Replicas: the set of all replicas (Replica IDs)                  *)
(*        Clients: the set of all clients (Client IDs)                     *)
(*        Quorums: the set of all quorums                                  *)
(*        SuperQuorums: the set of all super quorums                       *)
(*        Results: the set of all possible result types                    *)
(*        OperationBody: the set of all possible operation bodies          *)
(*          (with arguments, etc. - can be infinite)                       *)
(*        S: shard id of the shard Replicas constitute                     *)
(*        f: maximum number of failures allowed (half of n)                *)
(*                                                                         *)
(*  Constants used to bound variables, for model checking (Nat is bounded) *)
(*        max_vc: maximum number of View-Changes allowed for each replicas *)
(*        max_req: maximum number of op requests performed by clients      *)
(***************************************************************************)

CONSTANTS Replicas, Clients, Quorums, Operations, f, max_req, max_vc, max_c
         
ASSUME IsFiniteSet(Replicas)

ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Replicas
          /\ \A Q1, Q2 \in Quorums: Q1 \cap Q2 # {}

(***************************************************************************)
(* The  possible states of a replica and the two types of operations       *)
(*  currently defined by IR.                                               *)
(***************************************************************************)

ReplicaState == {"NORMAL", "FAILED", "RECOVERING", "VIEW-CHANGING"}
ClientState == {"NORMAL", "FAILED"}

(***************************************************************************)
(* Definition of operation space                                           *)
(***************************************************************************)

Operation == [op: Nat,
              c: Nat,
              s: Nat] \cup {<<>>}

(***************************************************************************)
(* Message is defined to be the set of all possible messages               *)
(***************************************************************************)

\* TODO: Assumptions
\* Assume unique message ids
\* Assume no more than f replica failures
Message ==
       [type: {"REQUEST"},
        op: Nat,
        c:  Clients,
        s:  Nat]
  \cup [type: {"REPLY"},
        v: Nat,
        s: Nat,
        x: Nat,
        dst: Clients] 
  \cup
       [type: {"PREPARE"},
        v: Nat,
        m: Operation,
        n: Nat,
        k: Nat]
  \cup
       [type: {"PREPARE-OK"},
        v: Nat,
        n: Nat,
        src: Replicas]
  \cup
       [type: {"COMMIT"},
        v: Nat,
        k: Nat]
  \cup
       [type: {"START-VIEW-CHANGE"},
        v: Nat,
        src: Replicas]
  \cup
       [type: {"DO-VIEW-CHANGE"},
        v: Nat,
        l: [1..max_req -> Operation],
        vp: Nat,
        n: Nat,
        k: Nat,
        src: Replicas,
        dst: Replicas]
  \cup
       [type: {"START-VIEW"},
        v: Nat,
        l: [1..max_req -> Operation],
        n: Nat,
        k: Nat, 
        src: Replicas]
  \cup 
       [type: {"RECOVERY"},
        x: Nat, \* nonce
        src: Replicas]
  \cup
       [type: {"RECOVERY-RESPONSE"},
        v: Nat,
        x: Nat,
        l: [1..max_req -> Operation],
        n: Nat,
        k: Nat,        
        dst: Replicas,
        src: Replicas]
  \cup 
       [type: {"STATE-REQUEST"},
        v: Nat,
        n: Nat,
        src: Replicas]
  \cup
       [type: {"STATE-RESPONSE"},
        v: Nat,
        l: [1..max_req -> Operation],
        n: Nat,
        k: Nat,
        src: Replicas]

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Variables and State Predicates}} ^'           *)
(***************************************************************************)

(***************************************************************************)
(* Variables:                                                              *)
(*        1. State at each replica:                                        *)
(*            rStatus = Denotes current replica state. Either:             *)
(*                       - NORMAL (processing operations)                  *)
(*                       - VIEW-CHANGING (participating in recovery)       *)
(*                       - RECOVERING (recovering replica)                 *)
(*            rLog = operations log and their results                      *)
(*            rViewNr = current view number                                *)
(*            rOpNr = assigned to the most recently received request       *)
(*            rCommitNr = the OpNr of the most recently commited op        *)
(*            rClientTable = for each client, the number of its most recent*)
(*                           request                                       *)
(*        2. State of communication medium:                                *)
(*            sentMsg = sent (but not yet received) messages               *)
(*        3. State at client:                                              *)
(*            cCrtOp = crt operation requested by the client               *)
(*            cReqNr = crt request number                                  *)
(*                                                                         *)
(***************************************************************************)

VARIABLES rStatus, rLog, rViewNr, rOpNr, rLastView, rReplies,
          rClientTable, rCommitNr, rNonce, rCrtOp,
          sentMsg,
          cCrtOp, cReqNr, cStatus,
          aSuccessful,
          gViewChangesNo,
          gCrashesNo

(***************************************************************************)
(* Defining these tuples makes it easier to express which varibles remain  *)
(* unchanged                                                               *)
(***************************************************************************)

\* Replica variables.
rVars == <<rStatus, rLog, rViewNr, rOpNr, rLastView,
           rClientTable, rCommitNr, rReplies, rNonce, rCrtOp>>
\* Client variables.
cVars == <<cCrtOp,        \* current operation at a client
           cReqNr,
           cStatus>>
\* Application variables
aVars == <<aSuccessful>>  \* we'll use them to write invariants
\* Other variables.
oVars == <<sentMsg, gViewChangesNo, gCrashesNo>>
\* All variables.
vars == <<rVars, cVars, aVars, oVars>>

TypeOK ==
  /\ rStatus \in [Replicas -> ReplicaState]
  /\ rLog \in [Replicas ->  [1..max_req -> Operation]]
  /\ rViewNr \in [Replicas -> Nat]
  /\ rOpNr \in [Replicas -> Nat]
  /\ rCommitNr \in [Replicas -> Nat]
  /\ rLastView \in [Replicas -> Nat]
  /\ rReplies \in [Replicas -> SUBSET ([type: {"prepare-ok"},
                                        v: Nat,
                                        n: Nat,
                                        src: Replicas]
                                  \cup [type: {"start-view-change"},
                                        v: Nat,
                                        src: Replicas]
                                  \cup [type: {"do-view-change"},
                                        v: Nat,
                                        l: [1..max_req -> Operation],
                                        vp: Nat,
                                        n: Nat,
                                        k: Nat,
                                        src: Replicas]
                                  \cup [type: {"recovery-response"},
                                        v: Nat,
                                        x: Nat,
                                        l: [1..max_req -> Operation],
                                        n: Nat,
                                        k: Nat,
                                        src: Replicas])]
  /\ rNonce \in [Replicas -> Nat]
  /\ rClientTable \in [Replicas -> [Clients -> Nat]]
  /\ rCrtOp \in [Replicas -> Operation]
  /\ sentMsg \in SUBSET Message                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  
  /\ cCrtOp \in [Clients -> Operation]
  /\ cReqNr \in [Clients -> Nat]
  /\ cStatus \in [Clients -> ClientState]
  /\ aSuccessful \in SUBSET Operation
  /\ gViewChangesNo \in Nat
  /\ gCrashesNo \in Nat

Init ==
  /\ rStatus = [r \in Replicas |-> "NORMAL"]
  /\ rLog = [r \in Replicas |-> [i \in 1..max_req |-> <<>>]]
  /\ rViewNr = [r \in Replicas |-> 0]
  /\ rLastView = [r \in Replicas |-> 0]
  /\ rOpNr = [r \in Replicas |-> 0]
  /\ rCommitNr = [r \in Replicas |-> 0]
  /\ rReplies = [r \in Replicas |-> {}]
  /\ rNonce = [r \in Replicas |-> 0]
  /\ rClientTable = [r \in Replicas |-> [c \in Clients |-> 0]]
  /\ rCrtOp = [r \in Replicas |-> <<>>]
  /\ sentMsg = {}
  /\ cCrtOp = [c \in Clients |-> <<>>]
  /\ cReqNr = [c \in Clients |-> 0]
  /\ cStatus = [c \in Clients |-> "NORMAL"]
  /\ aSuccessful = {}
  /\ gViewChangesNo = 0
  /\ gCrashesNo = 0

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Actions}} ^'                                  *)
(***************************************************************************)

Send(m) == sentMsg' = sentMsg \cup {m}
AmLeader(r, v) == r = (v % Cardinality(Replicas)) + 1
IsLeader(r, v) == AmLeader(r, v)
LeaderOf(v) == CHOOSE x \in Replicas: IsLeader(x, v)
-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Client Actions}} ^'                           *)
(***************************************************************************)

\* Note: CHOOSE does not introduce nondeterminism (the same value is chosen
\* each time)

\*Client sends a request
ClientRequest(c) ==
  \E op \in Operations:
    /\ cCrtOp[c] = <<>> \* the client is not waiting for a result
                        \* of another operation
    /\ cReqNr' = [cReqNr EXCEPT ![c] = @ + 1]
    /\ cCrtOp' = [cCrtOp EXCEPT ![c] = [op |-> op,
                                        c  |-> c,
                                        s |-> cReqNr[c] + 1]]
    /\ Send([type |-> "REQUEST",
             op |-> op,
             c  |-> c,
             s  |-> cReqNr[c] + 1])
    /\ UNCHANGED <<cStatus, rVars, aVars, gViewChangesNo, gCrashesNo>>
    /\ cReqNr[c] < max_req \* BOUND the number of requests a client can make

\*Client received a reply
ClientReceiveReply(c) ==
  \E msg \in sentMsg:
    /\ msg.type = "REPLY"
    /\ msg.s = cReqNr[c] \* reply to c's request for crt op
    /\ cCrtOp[c] /= <<>> 
    /\ cCrtOp' = [cCrtOp EXCEPT ![c] = <<>>]
    /\ aSuccessful' = aSuccessful \cup {cCrtOp[c]}
    /\ UNCHANGED <<cReqNr, cStatus, rVars, oVars>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Replica Actions}} ^'                          *)
(***************************************************************************)

(***************************************************************************)
(* Normal Operation protocol                                               *)
(***************************************************************************)

\* Replica sends prepares
ReplicaReceiveRequest(r) ==
  /\ r = 1
  /\ AmLeader(r, rViewNr[r])
  /\ \A replica \in {3}: /\ rViewNr[replica] = 0 /\ rStatus[replica] = "NORMAL"\* PRUNE send request only after view-change
                         /\ \E reply \in rReplies[2]: reply.type="do-view-change" /\ reply.src = replica
  /\ rCrtOp[r] = <<>>
  /\ \E msg \in sentMsg:
     /\ msg.type = "REQUEST"
     /\ msg.s > rClientTable[r][msg.c]
     /\ LET operation == [op |-> msg.op,
                          c |-> msg.c,
                          s |-> msg.s]
        IN
          /\ rCrtOp' = [rCrtOp EXCEPT ![r] = operation]
          /\ rLog' = [rLog EXCEPT ![r][rOpNr[r] + 1] = operation]
          /\ Send([type |-> "PREPARE",
                   v    |-> rViewNr[r],
                   m    |-> operation,
                   n    |-> rOpNr[r] + 1,
                   k    |-> rCommitNr[r]])
     /\ rClientTable' = [rClientTable EXCEPT ![r][msg.c] = msg.s]
     /\ rOpNr' = [rOpNr EXCEPT ![r] = @ + 1]
  /\ UNCHANGED <<rStatus, rLastView, rReplies,
                 rNonce, rViewNr, rCommitNr, cVars, aVars, gViewChangesNo, gCrashesNo>>

\* Replica receives a prepare request from the leader
ReplicaReceivePrepare(r) ==
  /\ r \in {1,3} \* PRUNE
  /\ \E msg \in sentMsg:
     /\ msg.type = "PREPARE"
     /\ \/ /\ msg.v > rViewNr[r] \/ msg.n > rOpNr[r] + 1 \* Need state transfer
                                                         \* (miss a prepare or in a lower view)
           /\ Send([type |-> "STATE-REQUEST",
                    v    |-> rViewNr[r],
                    n    |-> rOpNr[r],
                    src  |-> r])
           /\ UNCHANGED <<rVars, cVars, aVars, gViewChangesNo>>
        \/ /\ msg.v = rViewNr[r] /\ \/ msg.n = rOpNr[r] + 1
                                    \/ msg.n = rOpNr[r]
           /\ rLog' = [rLog EXCEPT ![r][msg.n] = msg.m]
           /\ rOpNr' = [rOpNr EXCEPT ![r] = msg.n]
           /\ rClientTable' = [rClientTable EXCEPT ![r][msg.m.c] = msg.m.s]
           /\ Send([type |-> "PREPARE-OK",
                    v    |-> rViewNr[r],
                    n    |-> msg.n,
                    src  |-> r])
           /\ UNCHANGED <<rCrtOp, rStatus, rViewNr, rLastView,
                          rReplies, rCommitNr,
                          rNonce, cVars, aVars, gViewChangesNo, gCrashesNo>>

ReplicaReceiveStateRequest(r) ==
  \E msg \in sentMsg:
     /\ msg.type = "STATE-REQUEST"
     /\ msg.v < rViewNr[r] /\ msg.n < rOpNr[r]
     /\ Send([type |-> "STATE-RESPONSE",
              v    |-> rViewNr[r],
              l    |-> rLog[r],
              n    |-> rOpNr[r],
              k    |-> rCommitNr[r],
              src  |-> r])
     /\ UNCHANGED <<rVars, cVars, aVars, gViewChangesNo, gCrashesNo>>
 
ReplicaReceiveStateResponse(r) ==
  \E msg \in sentMsg: \* TODO: some more cases to check to merge
                      \* these - for now don't need, just one operation req 
     /\ msg.type = "STATE-RESPONSE"
     /\ \/ msg.v = rViewNr[r] /\ msg.n > rOpNr[r]
        \/ msg.v > rViewNr[r]
     /\ rViewNr' = [rViewNr EXCEPT ![r] = msg.v]
     /\ rLog' = [rLog EXCEPT ![r] = msg.l]
     /\ rOpNr' = [rOpNr EXCEPT ![r] = msg.n]
     /\ UNCHANGED <<rClientTable, rCrtOp, rCommitNr,
                    rStatus, rLastView, rReplies,
                    rNonce, cVars, aVars, oVars>>   

\* Leader receives a prepare ok
ReplicaReceivePrepareOK(r) ==
  /\ \E msg \in sentMsg:
     /\ msg.type = "PREPARE-OK"
     /\ msg.v = rViewNr[r]
     /\ msg.n = rOpNr[r]
     /\ AmLeader(r, msg.v)
     /\ rReplies' = [rReplies EXCEPT ![r] = @ \cup
                            {[type |-> "prepare-ok",
                               v |->  msg.v,
                               n |->  msg.n,
                               src |-> msg.src
                             ]}]
     /\ UNCHANGED <<rClientTable, rCrtOp, rOpNr, rCommitNr,
                    rStatus, rLastView, rLog, rViewNr,
                    rNonce, cVars, aVars, oVars>>


\* Leader received enough replies
ReplicaSendReply(r) ==
   /\ AmLeader(r, rViewNr[r])
   /\ \E Q \in Quorums:
    /\ \A rep \in Q: \E reply \in rReplies[r]:
      /\ reply.src = rep
      /\ reply.type = "prepare-ok"
      /\ reply.v = rViewNr[r]
      /\ reply.n = rOpNr[r]
   /\ Send([type |-> "REPLY",
            v    |-> rViewNr[r],
            s    |-> rLog[r][rOpNr[r]].s,
            x    |-> 1,
            dst  |-> rLog[r][rOpNr[r]].c])
   /\ UNCHANGED <<rVars, cVars, aVars, gViewChangesNo, gCrashesNo>>

(***************************************************************************)
(* View-change protocol                                                    *)
(***************************************************************************)
\* A replica starts a view change procedure
ReplicaSendStartViewChange(r) ==
  /\ r \in {2, 3} \* PRUNE just replicas 2 and 3 start a view change
  /\ rViewNr' = [rViewNr EXCEPT ![r] = @ + 1]
  /\ Send([type |-> "START-VIEW-CHANGE",
           v    |-> rViewNr[r] + 1,
           src  |-> r])
  /\ rStatus' = [rStatus EXCEPT ![r] = "VIEW-CHANGING"]
  /\ UNCHANGED <<rReplies, rNonce, rClientTable,
                 rCrtOp, rOpNr, rCommitNr,
                 rLastView, rLog, cVars, aVars, gCrashesNo>>
  /\ gViewChangesNo < max_vc \* BOUND on number of view changes
  /\ gViewChangesNo' = gViewChangesNo + 1

\* A replica received a message to start view change
ReplicaReceiveStartViewChange(r) ==
  /\ r \in {2, 3} \* PRUNE just these paricipate in a view change
  /\ \E r1 \in {2, 3}: 
       rStatus[r1] = "NORMAL" \* PRUNE
  /\ \E msg \in sentMsg:
    /\ msg.type = "START-VIEW-CHANGE"
    /\ \/ /\ rStatus[r] = "NORMAL"
          /\ msg.v > rViewNr[r]
          /\ rStatus' = [rStatus EXCEPT ![r] = "VIEW-CHANGING"]
       \/ /\ rStatus[r] = "VIEW-CHANGING"
          /\ msg.v >= rViewNr[r]
          /\ UNCHANGED <<rStatus>>
    /\ rReplies' = [rReplies EXCEPT ![r] = @ \cup
                            {[type |-> "start-view-change",
                              v    |-> msg.v,
                              src  |-> msg.src]}]
    /\ rViewNr' = [rViewNr EXCEPT ![r] = msg.v]
    /\ Send([type |-> "START-VIEW-CHANGE",
             v    |-> msg.v,
             src  |-> r])
  /\ UNCHANGED <<rClientTable, rCrtOp, rOpNr, rCommitNr, 
                 rNonce, rLog, rLastView, cVars,
                 aVars, gViewChangesNo, gCrashesNo>>

\* We received enough view change replies to be able to
\* send a do-view-change 
ReplicaSendDoViewChange(r) ==
  /\ r \in {2,3} \* PRUNE just these participate in a view change
  /\ \E Q \in Quorums:
    /\ r \in Q
    /\ \A rep \in Q: rep = r \/ \E reply \in rReplies[r]:
      /\ reply.src = rep
      /\ reply.type = "start-view-change"
      /\ reply.v = rViewNr[r]
  /\ Send([type |-> "DO-VIEW-CHANGE",
           v    |-> rViewNr[r],
           l    |-> rLog[r],
           vp   |-> rLastView[r],
           n    |-> rOpNr[r],
           k    |-> rCommitNr[r],
           src  |-> r,
           dst  |-> LeaderOf(rViewNr[r])])
  /\ UNCHANGED <<rVars, cVars, aVars, gViewChangesNo, gCrashesNo>>

\* Replica received DO-VIEW-CHANGE message
ReplicaReceiveDoViewChange(r) ==
  /\ r = 2 \* PRUNE just the new leader switches view
  \* /\ \A rr \in {2,3}: rStatus[rr] = "NORMAL" /\ rNonce[rr] > 0 /\ rViewNr[rr] = 0
  /\ \E msg \in sentMsg:
       /\ msg.type = "DO-VIEW-CHANGE"
       /\ msg.dst = r
       /\ \/ /\ rStatus[r] = "NORMAL"
             /\ msg.v > rViewNr[r]
          \/ /\ rStatus[r] = "VIEW-CHANGING"
             /\ msg.v >= rViewNr[r]
       /\ rStatus' = [rStatus EXCEPT ![r] = "VIEW-CHANGING"]
       \* keep only the one with the higher view (v)
       /\ LET
            existingRecord == {x \in rReplies[r]:
                                /\ x.type = "do-view-change"
                                /\ x.src = msg.src} \* should only be one item in set
          IN
            IF \A x \in existingRecord: x.v < msg.v
            THEN rReplies' = [rReplies EXCEPT ![r] =
                                        (@ \ existingRecord) \cup
                                          {[type       |-> "do-view-change",
                                            v          |-> msg.v,
                                            l          |-> msg.l,
                                            vp         |-> msg.vp,
                                            n          |-> msg.n,
                                            k          |-> msg.k,
                                            src        |-> msg.src]}]
            ELSE FALSE
  /\ UNCHANGED <<cVars, rClientTable, rCrtOp, rOpNr, rCommitNr,
                 rViewNr, rLastView, rLog, rNonce, aVars, oVars>>

\* Note: Assume one reply for view change per replica in Q
\* (in ReplicaReceiveDoViewChange we keep only the most recent reply)
ReplicaSendStartView(r) ==
  /\ \E Q \in Quorums:
    /\ r \in Q
    /\ \A r1 \in Q:
      /\ \A r2 \in Q: \E rr, pr \in rReplies[r]:
                                  /\ rr.type = "do-view-change"
                                  /\ pr.type = "do-view-change"
                                  /\ rr.src = r1
                                  /\ pr.src = r2
                                  /\ rr.v = pr.v
                                  \*/\ rr.v > rLastView[r]
                                  /\ AmLeader(r, rr.v)
    \* received at a least a quorum of replies
    /\ LET
           A ==
             \* set of all do-view-change replies from Q
             {x \in rReplies[r]: /\ x.src \in Q
                                 /\ x.type = "do-view-change"}

           B ==
             \* set of all do-view-change replies in A that have the biggest vp
             {x \in A: \A rep \in A: rep.vp <= x.vp}

           replyWithMostCompleteLog ==
           \* if multiple replies in B, choose the one with the largest op number
              CHOOSE x \in B: \A rep \in B: rep.n <= x.n

           ops(c) ==
             {x \in Operation: 
               \E i \in 1..max_req: 
                  /\ replyWithMostCompleteLog.l[i] = x
                  /\ x /= <<>>
                  /\ x.c = c}

           v_new ==
             \* the one decided by quorum Q
             CHOOSE v \in {x.v: x \in A}: TRUE
       IN
           /\ rLog' = [rLog EXCEPT ![r] = replyWithMostCompleteLog.l]
           /\ Send([type |-> "START-VIEW",
                    v    |-> v_new,
                    l    |-> replyWithMostCompleteLog.l,
                    n    |-> replyWithMostCompleteLog.n,
                    k    |-> replyWithMostCompleteLog.k,
                    src  |-> r])
           /\ rOpNr' = [rOpNr EXCEPT ![r] = replyWithMostCompleteLog.n]
           /\ rCommitNr' = [rCommitNr EXCEPT ![r] = replyWithMostCompleteLog.k]
           /\ rViewNr' = [rViewNr EXCEPT ![r] = v_new]
           /\ rLastView' = [rLastView EXCEPT ![r] = v_new]
           \* Update client table based on the latest op commited from each client
           /\ rClientTable' = [rClientTable EXCEPT ![r] = [c \in Clients |-> 
                                 IF ops(c) /= {}
                                 THEN CHOOSE s \in {op.s: op \in ops(c)}:
                                               \A op \in ops(c): op.s <= s  
                                 ELSE 0]]
  /\ rCrtOp' = [rCrtOp EXCEPT ![r] = <<>>]
  /\ rStatus' = [rStatus EXCEPT ![r] = "NORMAL"]
  /\ rReplies' = [rReplies EXCEPT ![r] = {}]
  /\ UNCHANGED <<rNonce, cVars, aVars, gViewChangesNo, gCrashesNo>>

\*A replica receives a start view message
ReplicaReceiveStartView(r) ==
  /\ aSuccessful /= {} \* PRUNE possible paths
  /\ \E msg \in sentMsg:
    /\ msg.type = "START-VIEW"
    /\ \/ /\ rStatus[r] = "NORMAL"
          /\ msg.v > rViewNr[r]
       \/ /\ \/ rStatus[r] = "VIEW-CHANGING"
             \/ rStatus[r] = "RECOVERING"
          /\ msg.v >= rViewNr[r]
    /\ rViewNr' = [rViewNr EXCEPT ![r] = msg.v]
    /\ rLastView' = [rLastView EXCEPT ![r] = msg.v]
    /\ rLog' = [rLog EXCEPT ![r] = msg.l]
    /\ LET ops(c) ==
             {x \in Operation: 
               \E i \in 1..max_req: 
                  /\ msg.l[i] = x
                  /\ x /= <<>>
                  /\ x.c = c}
       IN
         rClientTable' = [rClientTable EXCEPT ![r] = [c \in Clients |-> 
                            IF ops(c) /= {}
                            THEN CHOOSE s \in {op.s: op \in ops(c)}:
                                          \A op \in ops(c): op.s <= s  
                            ELSE 0]]
  /\ rStatus' = [rStatus EXCEPT ![r] = "NORMAL"]
  /\ rReplies' = [rReplies EXCEPT ![r] = {}]
  /\ UNCHANGED <<rCrtOp, rOpNr, rCommitNr,
                 rNonce, cVars, aVars, oVars>>

(***************************************************************************)
(* Recovery protocol                                                       *)
(***************************************************************************)
\*A replica fails and looses everything
ReplicaFail(r) ==
  /\ r \in {2,3} \* PRUNE just these are allowed to fail
  /\ rNonce[r] < 3 \* BOUND
  /\ gCrashesNo < max_c \* BOUND
  /\ gCrashesNo' = gCrashesNo + 1
  \*/\ \E msg \in sentMsg: msg.type = "START-VIEW-CHANGE" /\ msg.src = r \* PRUNE
  /\ rStatus' = [rStatus EXCEPT ![r] = "FAILED"]
  /\ rViewNr' = [rViewNr EXCEPT ![r] = 0]
  /\ rReplies' = [rReplies EXCEPT ![r] = {}]
  /\ rCrtOp' = [rCrtOp EXCEPT ![r] = <<>>]
  /\ rCommitNr' = [rCommitNr EXCEPT ![r] = 0]
  /\ rOpNr' = [rOpNr EXCEPT ![r] = 0]
  /\ rClientTable' = [rClientTable EXCEPT![r] = [c \in Clients |-> 0]]
  /\ rLog' = [rLog EXCEPT![r] = [i \in 1..max_req |-> <<>>]]
  /\ UNCHANGED <<rLastView, rNonce, cVars, aSuccessful, sentMsg, gViewChangesNo>>
  /\ \* We assume less than f replicas fail simultaneously
     Cardinality({re \in Replicas:
                           \/ rStatus[re] = "FAILED"
                           \/ rStatus[re] = "RECOVERING"}) < f

\* Recovery protocol
ReplicaRecover(r) ==
  /\ Send([type |-> "RECOVERY",
           x    |-> rNonce[r] + 1,
           src  |-> r])
  /\ rStatus' = [rStatus EXCEPT ![r] = "RECOVERING"]
  /\ rNonce' = [rNonce EXCEPT ![r] = @ + 1]
  /\ UNCHANGED <<rLog, rViewNr, rReplies,
                 rClientTable, rCrtOp,
                 rLastView, rCommitNr,
                 rOpNr,
                 cVars, aVars,
                 gViewChangesNo, gCrashesNo>>

ReplicaSendRecoveryResponse(r) ==
  /\ rViewNr[r] = 0
  /\ \E msg \in sentMsg:
     /\ msg.type = "RECOVERY"
     \* TODO: send nil if not leader,
     \* does not really matter for our purposes
     \* right now
     /\ Send([type |-> "RECOVERY-RESPONSE",
              v    |-> rViewNr[r],
              x    |-> msg.x,
              l    |-> rLog[r],
              n    |-> rOpNr[r],
              k    |-> rCommitNr[r],
              src  |-> r,
              dst  |-> msg.src])
     /\ UNCHANGED <<rVars, cVars, aVars, gViewChangesNo, gCrashesNo>>

ReplicaReceiveRecoveryResponse(r) ==
    \E msg \in sentMsg:
     /\ msg.type = "RECOVERY-RESPONSE"
     /\ msg.x = rNonce[r]
     /\ msg.dst = r
     /\ rReplies' = [rReplies EXCEPT ![r] = @ \cup
                            {[type |-> "recovery-response",
                               v |->  msg.v,
                               x |-> msg.x,
                               l |-> msg.l,
                               n |-> msg.n,
                               k |-> msg.k,
                               src  |-> msg.src]}]
     /\ UNCHANGED <<rStatus, rLastView, rLog, rViewNr,
                    rClientTable, rCrtOp, rOpNr, rCommitNr,
                    rNonce, cVars, aVars, oVars>>
   

ReplicaFinishRecovery(r) ==
  /\ \E Q \in Quorums:
    /\ \A rep \in Q: \E reply \in rReplies[r]:
      /\ reply.type = "recovery-response"
      /\ reply.src = rep
      /\ reply.x = rNonce[r]
    \* received at a least a quorum of replies
    /\ LET
           A ==
             \* set of all recovery-response replies from Q
             {x \in rReplies[r]: /\ x.src \in Q
                                 /\ x.type = "recovery-response"
                                 /\ x.x = rNonce[r]}

           B ==
             \* set of all recovery-response replies in A from the biggest view
             {x \in A: \A rep \in A: rep.v <= x.v}

           leaderReply == 
             \* reply from leader
             IF ~ \E x \in B: IsLeader(x.src, x.v)
             THEN <<>>
             ELSE CHOOSE x \in B: IsLeader(x.src, x.v)

       IN
           /\ leaderReply /= <<>>
           /\ Assert(leaderReply.v = 0, "Assert that we recover just in view 0")
           /\ rLog' = [rLog EXCEPT ![r] = leaderReply.l]
           /\ rOpNr' = [rOpNr EXCEPT ![r] = leaderReply.n]
           /\ rViewNr' = [rViewNr EXCEPT ![r] = leaderReply.v]
           /\ rLastView' = [rLastView EXCEPT ![r] = leaderReply.v]
           \* TODO: rClientTable
  /\ rStatus' = [rStatus EXCEPT ![r] = "NORMAL"]
  /\ rReplies' = [rReplies EXCEPT ![r] = {}]
  /\ UNCHANGED <<rNonce, cVars, aVars, gViewChangesNo, gCrashesNo, sentMsg, rClientTable,
                 rCrtOp, rCommitNr>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{High-Level Actions}} ^'                       *)
(***************************************************************************)

ClientAction(c) ==
  \/ /\ cStatus[c] = "NORMAL"
     /\ \/ ClientRequest(c) \* some client tries to replicate commit an operation
        \/ ClientReceiveReply(c)  \* some client receives a reply from a replica
        \*\/ ClientFail(c)     \* some client fails
  \/ /\ cStatus[c] = "FAILED"
     \*/\ \/ ClientRecover(c)

ReplicaAction(r) ==
  \/ /\ rStatus[r] = "NORMAL"
     /\ \/ ReplicaReceiveRequest(r)
        \/ ReplicaSendReply(r)
        \/ ReplicaReceivePrepare(r)
        \/ ReplicaReceivePrepareOK(r)
        \/ ReplicaSendStartViewChange(r)
        \/ ReplicaReceiveStartViewChange(r)
        \/ ReplicaSendDoViewChange(r)
        \/ ReplicaReceiveDoViewChange(r)
        \/ ReplicaSendStartView(r)
        \/ ReplicaReceiveStartView(r)
        \/ ReplicaSendRecoveryResponse(r)
        \/ ReplicaReceiveStateRequest(r)
        \/ ReplicaReceiveStateResponse(r)
        \*\/ ReplicaFail(r)       \* some replica fails
  \/ /\ rStatus[r] = "FAILED"
     /\ \/ ReplicaRecover(r) \* start view-change protocol
  \/ /\ rStatus[r] = "RECOVERING"
     /\ \/ ReplicaReceiveRecoveryResponse(r) \* Replica received a
                                             \* recovery response
        \/ ReplicaFinishRecovery(r)
  \/ /\ rStatus[r] = "VIEW-CHANGING"
     /\ \/ ReplicaReceiveStartViewChange(r)
        \/ ReplicaSendDoViewChange(r)
        \/ ReplicaReceiveDoViewChange(r)
        \/ ReplicaSendStartView(r)
        \/ ReplicaReceiveStartView(r)
        \/ ReplicaFail(r)

Next ==
     \/ \E c \in Clients: ClientAction(c)
     \/ \E r \in Replicas: ReplicaAction(r)
     \/ \* Avoid deadlock by termination
       (\A i \in 1..Cardinality(Replicas): rLastView[i] = max_vc) /\ UNCHANGED <<vars>>

Spec == Init /\ [] [Next]_vars

FaultTolerance ==
  /\ \A successfulOp \in aSuccessful, Q \in Quorums:
         (\A r \in Q: rStatus[r] = "NORMAL" \/ rStatus[r] = "VIEW-CHANGING")
      => (\E r \in Q: \E i \in 1..max_req: rLog[r][i] = successfulOp)

Inv == FaultTolerance

Inv2 == aSuccessful = {}

=============================================================================
\* Modification History
\* Last modified Sat Aug 01 13:57:28 PDT 2015 by aaasz
\* Created Fri Dec 12 17:42:14 PST 2014 by aaasz
