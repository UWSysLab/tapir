------------------------ MODULE IR_consensus --------------------------------
(***************************************************************************)
(* This is a TLA+ specification of the Inconsistent Replication algorithm. *)
(* (And a mechanically-checked proof of its correctness using TLAPS)       *)
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

CONSTANTS Replicas, Clients, Quorums, SuperQuorums, Results, OpBody,
          AppClientFail, AppReplicaFail,
          SuccessfulInconsistentOp(_,_,_), SuccessfulConsensusOp(_,_,_,_),
          Merge(_,_,_),
          Sync(_),
          ExecInconsistent(_),
          ExecConsensus(_),
          Decide(_),
          f,
          S, Shards, \* S = shard id
          max_vc, max_req

ASSUME IsFiniteSet(Replicas)

ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Replicas
          /\ SuperQuorums \subseteq SUBSET Replicas
          /\ \A Q1, Q2 \in Quorums: Q1 \cap Q2 # {}
          /\ \A Q \in Quorums, R1, R2 \in SuperQuorums:
                                         Q \cap R1 \cap R2 # {}

ASSUME FailuresAssumption ==
          \A Q \in Quorums: Cardinality(Q) > f

(***************************************************************************)
(* The  possible states of a replica and the two types of operations       *)
(*  currently defined by IR.                                               *)
(***************************************************************************)

ReplicaState == {"NORMAL", "FAILED", "RECOVERING", "VIEW-CHANGING"}
ClientState == {"NORMAL", "FAILED"}
OpType == {"Inconsistent", "Consensus"}
OpStatus == {"TENTATIVE", "FINALIZED"}

(***************************************************************************)
(* Definition of operation space                                           *)
(***************************************************************************)

MessageId == [cid: Clients, msgid: Nat]
Operations == [type: OpType, body: OpBody] \cup {<<>>}

(***************************************************************************)
(* Message is defined to be the set of all possible messages               *)
(***************************************************************************)

\* Assume unique message ids
\* Assume no more than f replica failures
\* We use shard to specify for what shard this message was
\*  (we share the variables)
Message ==
       [type: {"PROPOSE"},
        id: MessageId,
        op: Operations,
        v:  Nat]
  \cup [type: {"REPLY"}, \* reply no result
        id: MessageId,
        v: Nat,
        src: Replicas] 
  \cup
       [type: {"REPLY"}, \* reply with result
        id: MessageId,
        v: Nat,
        res: Results,
        src: Replicas]
       \* v = view num.
  \cup
       [type: {"START-VIEW-CHANGE"},
        v: Nat,
        src: Replicas]
  \cup
       [type: {"DO-VIEW-CHANGE"},
        r: SUBSET ([msgid: MessageId,
                    op: Operations,
                    res: Results,
                    status: OpStatus]
              \cup [msgid: MessageId,
                    op: Operations,
                    status: OpStatus]),
        v: Nat,
        lv: Nat,
        src: Replicas,
        dst: SUBSET Replicas]
  \cup
       [type: {"START-VIEW"},
        v: Nat,
        r: SUBSET ([msgid: MessageId,
                    op: Operations,
                    res: Results,
                    status: OpStatus]
              \cup [msgid: MessageId,
                    op: Operations,
                    status: OpStatus]), 
        src: Replicas]
  \cup
       [type: {"FINALIZE"}, \* finalize with no result
        id: MessageId,
        op: Operations,
        res: Results,
        v: Nat]
  \cup
       [type: {"FINALIZE"}, \* finalize with result
        id: MessageId,
        op: Operations,
        res: Results,
        v: Nat]
  \cup
       [type: {"CONFIRM"},
        v: Nat,
        id: MessageId,
        op: Operations,
        res: Results,
        src: Replicas]

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Variables and State Predicates}} ^'           *)
(***************************************************************************)

(***************************************************************************)
(* \* Variables:                                                           *)
(*        1. State at each replica:                                        *)
(*            rState = Denotes current replica state. Either:              *)
(*                       - NORMAL (processing operations)                  *)
(*                       - VIEW-CHANGING (participating in recovery)       *)
(*            rRecord = Unordered set of operations and their results      *)
(*            rViewNumber = current view number                            *)
(*        2. State of communication medium:                                *)
(*            sentMsg = sent (but not yet received) messages               *)
(*        3. State at client:                                              *)
(*            cCurrentOperation = crt operation requested by the client    *)
(*            cMmessageCounter = the message I must use for                *)
(*                               the next operation                        *)
(* *\                                                                      *)
(***************************************************************************)

VARIABLES rState, rRecord, rCrtView, rLastView, rViewReplies,
          rViewOnDisk,
          rNonce, sentMsg, cCrtOp,
          cCrtOpToFinalize, cMsgCounter, cCrtOpReplies, cCrtOpConfirms,
          cState, aSuccessful, arRecord, aVisibility, gViewChangesNo

(***************************************************************************)
(* Defining these tuples makes it easier to express which varibles remain  *)
(* unchanged                                                               *)
(***************************************************************************)

\* Replica variables.
rVars == <<rState, rRecord, rCrtView, rViewOnDisk, rLastView,
           rViewReplies, rNonce>>
\* Client variables.
cVars == <<cCrtOp,        \* current operation at a client
           cCrtOpToFinalize,
           cCrtOpReplies, \* current operation replies
           cCrtOpConfirms,
           cMsgCounter,
           cState>>
\* Application variables.
aVars == <<aSuccessful, arRecord, aVisibility>>  \* we use them to write invariants
\* Other variables.
oVars == <<sentMsg, gViewChangesNo>>
\* All variables.
vars == <<rVars, cVars, aVars, oVars>>

TypeOK ==
  /\ rState[S] \in [Replicas -> ReplicaState]
  /\ rRecord[S] \in [Replicas ->  SUBSET ([msgid: MessageId,
                                           op: Operations,
                                           res: Results,
                                           status: OpStatus]
                                     \cup [msgid: MessageId,
                                           op: Operations,
                                           status: OpStatus])]
  /\ rCrtView[S] \in [Replicas -> Nat]
  /\ rViewOnDisk[S] \in [Replicas -> Nat]  
  /\ rLastView[S] \in [Replicas -> Nat]
  /\ rViewReplies[S] \in [Replicas -> SUBSET ([type: {"start-view-change"},
                                               v: Nat,
                                               src: Replicas]
                                         \cup [type: {"do-view-change"},
                                               v: Nat,
                                               lv: Nat,
                                               r: SUBSET ([msgid: MessageId,
                                                           op: Operations,
                                                           res: Results,
                                                           status: OpStatus]
                                                     \cup [msgid: MessageId,
                                                           op: Operations,
                                                           status: OpStatus]),
                                               src: Replicas])]
  /\ rNonce[S] \in [Replicas -> Nat]
  /\ sentMsg[S] \in SUBSET Message
  /\ cCrtOp[S] \in [Clients -> Operations]
  /\ cCrtOpToFinalize[S] \in [Clients -> Operations]
  /\ cCrtOpReplies[S] \in [Clients -> SUBSET ([viewNumber: Nat,
                                              res: Results,
                                              src: Replicas]
                                        \cup [viewNumber: Nat,
                                              src: Replicas])]
  /\ cCrtOpConfirms[S] \in [Clients -> SUBSET [viewNumber: Nat,
                                              res: Results,
                                              src: Replicas]]
  /\ cMsgCounter[S] \in [Clients -> Nat]
  /\ cState \in [Clients -> ClientState]
  /\ aSuccessful \in SUBSET ([mid: MessageId,
                                  op: Operations,
                                 res: Results]
                           \cup [mid: MessageId,
                                  op: Operations])
  /\ aVisibility[S] \in [MessageId -> SUBSET MessageId]
  /\ arRecord[S] \in [Replicas ->  SUBSET ([msgid: MessageId,
                                            op: Operations,
                                            res: Results,
                                            status: OpStatus]
                                     \cup [msgid: MessageId,
                                           op: Operations,
                                           status: OpStatus])]
  /\ gViewChangesNo[S] \in Nat

Init ==
  /\ rState = [r \in Replicas |-> "NORMAL"]
  /\ rRecord = [r \in Replicas |-> {}]
  /\ rCrtView = [r \in Replicas |-> 0]
  /\ rViewOnDisk = [r \in Replicas |-> 0]
  /\ rLastView = [r \in Replicas |-> 0]
  /\ rViewReplies = [r \in Replicas |-> {}]
  /\ rNonce = [r \in Replicas |-> 0]
  /\ sentMsg = {}
  /\ cCrtOp = [c \in Clients |-> <<>>]
  /\ cCrtOpToFinalize = [c \in Clients |-> <<>>]
  /\ cCrtOpReplies = [c \in Clients |-> {}]
  /\ cCrtOpConfirms = [c \in Clients |-> {}]
  /\ cMsgCounter = [c \in Clients |-> 0]
  /\ cState = [c \in Clients |-> "NORMAL"]
  /\ aSuccessful = {}
  /\ aVisibility = [o \in MessageId |-> {}]
  /\ arRecord = [r \in Replicas |-> {}]
  /\ gViewChangesNo = 0

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Actions}} ^'                                  *)
(***************************************************************************)

Send(m) == sentMsg' = [sentMsg EXCEPT ![S] = @ \cup {m}]

AmLeader(r, v) == r = (v % Cardinality(Replicas)) + 1
IsLeader(r, v) == AmLeader(r, v)
NotIsLeader(r, v) == r /= (v % Cardinality(Replicas)) + 1
LeaderOf(v) == CHOOSE x \in Replicas: IsLeader(x, v)

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Client Actions}} ^'                           *)
(***************************************************************************)

\* Note: CHOOSE does not introduce nondeterminism (the same value is chosen
\* each time)

\* \* Client sends a request
ClientRequest(c, op) ==
  /\ cCrtOp[S][c] = <<>> \* the client is not waiting for a result
                         \* of another operation
  /\ cCrtOpToFinalize[S][c] = <<>> \* the client is not waiting
                                   \* to finalize operation
  /\ cMsgCounter' = [cMsgCounter EXCEPT ![S][c] = @ + 1]
  /\ cCrtOp' = [cCrtOp EXCEPT ![S][c] = op]
  /\ Send([type |-> "PROPOSE",
             id |-> [cid |-> c, msgid |-> cMsgCounter[S][c] + 1],
             op |-> op,
             v  |-> 0])
  /\ UNCHANGED <<rVars, aVars, cCrtOpReplies, cCrtOpToFinalize,
                 cCrtOpConfirms,cState, gViewChangesNo>>
  /\ cMsgCounter[S][c] < max_req \* BOUND the number of requests a client can make
                                 \* (useful for model checking)

\* \* Client received a reply
ClientReceiveReply(c) ==
  \E msg \in sentMsg[S]:
    /\ msg.type = "REPLY"
    /\ cCrtOp[S][c] /= <<>>
    /\ \* reply to c's request for crt op 
       msg.id = [cid |-> c, msgid |-> cMsgCounter[S][c]]
    /\ \/ /\ cCrtOp[S][c].type = "Inconsistent"
          /\ cCrtOpReplies' = [cCrtOpReplies EXCEPT ![S][c] = @ \cup 
                                           {[viewNumber |-> msg.v,
                                             src         |-> msg.src]}]
       \/ /\ cCrtOp[S][c].type = "Consensus"
          /\ cCrtOpReplies' = [cCrtOpReplies EXCEPT ![S][c] = @ \cup 
                                           {[viewNumber |-> msg.v,
                                             res         |-> msg.res,
                                             src         |-> msg.src]}]
    /\ UNCHANGED <<cCrtOp, cCrtOpToFinalize, cCrtOpConfirms,
                   cMsgCounter, cState, rVars, aVars, oVars>>

\* \* "Helper" formulas
__matchingViewNumbers(Q, c) ==
     \* a (super)quorum of replies with matching view numbers
     /\ \A r \in Q:
        \*/\ \E reply \in cCrtOpReplies[S][c]: reply.src = r
        /\ \A p \in Q: \E rr, pr \in cCrtOpReplies[S][c]:
                                  /\ rr.src = r
                                  /\ pr.src = p
                                  /\ rr.viewNumber = pr.viewNumber

__matchingViewNumbersAndResults(Q, c) ==
     \* a (super)quorum of replies with matching view numbers
     \* and results
     /\ \A r \in Q:
        \*/\ \E reply \in cCrtOpReplies[S][c]: reply.src = r
        /\ \A p \in Q: \E rr, pr \in cCrtOpReplies[S][c]:
                                  /\ rr.src = r
                                  /\ pr.src = p
                                  /\ rr.viewNumber = pr.viewNumber
                                  /\ rr.res = pr.res

\* \* IR Client received enough responses to decide
\* \* what to do with the operation
ClientSendFinalize(c) ==
  /\ cCrtOp[S][c] /= <<>>
  /\ \/ \E Q \in Quorums:
     \* I. The IR Client got a simple quorum of replies
        /\ \A r \in Q:
             \E reply \in cCrtOpReplies[S][c]: reply.src = r

        /\ \/ /\ cCrtOp[S][c].type = "Inconsistent"
              /\ __matchingViewNumbers(Q, c)
              /\ aSuccessful' = aSuccessful \cup
                                 {[mid |-> [cid |-> c,
                                   msgid |-> cMsgCounter[S][c]],
                                   op |-> cCrtOp[S][c]]}
              /\ SuccessfulInconsistentOp(c, S, cCrtOp[S][c])
              /\ Send([type |-> "FINALIZE",
                       id |-> [cid |-> c, msgid |-> cMsgCounter[S][c]],
                       op |-> cCrtOp[S][c],
                       v  |-> 0])
              /\ UNCHANGED <<cCrtOpToFinalize>>

           \/ /\ cCrtOp[S][c].type = "Consensus"
              /\ __matchingViewNumbers(Q, c)
              /\ LET res == IF __matchingViewNumbersAndResults(Q, c) 
                            THEN
                                CHOOSE result \in
                                    {res \in Results: 
                                        \E reply \in cCrtOpReplies[S][c]:
                                           /\ reply.src \in Q
                                           /\ reply.res = res}: TRUE
                            ELSE
                                 Decide(cCrtOpReplies[S][c])
                 IN
                   /\ Send([type |-> "FINALIZE",
                            id |-> [cid |-> c, msgid |-> cMsgCounter[S][c]],
                            op |-> cCrtOp[S][c],
                            res |-> res,
                            v  |-> 0])
              /\ cCrtOpToFinalize' = [cCrtOp EXCEPT ![S][c] = cCrtOp[S][c]]
              /\ UNCHANGED <<aSuccessful>>

     \/ \E SQ \in SuperQuorums:
     \* II. The IR Client got super quorum of responses
        /\ \A r \in SQ:
             \E reply \in cCrtOpReplies[S][c]: reply.src = r         
        /\ cCrtOp[S][c].type = "Consensus" \* only care if consensus op
        /\ __matchingViewNumbersAndResults(SQ, c)
        /\ LET res == CHOOSE result \in
                                    {res \in Results: 
                                        \E reply \in cCrtOpReplies[S][c]:
                                           /\ reply.src \in SQ
                                           /\ reply.res = res}: TRUE
           IN
             /\ Send([type |-> "FINALIZE",
                      id |-> [cid |-> c, msgid |-> cMsgCounter[S][c]],
                      op |-> cCrtOp[S][c],
                      res |-> res,
                      v  |-> 0])
             /\ aSuccessful' = aSuccessful \cup
                                 {[mid |-> [cid |-> c,
                                            msgid |-> cMsgCounter[S][c]],
                                   op |-> cCrtOp[S][c],
                                   res |-> res]}
             /\ SuccessfulConsensusOp(c, S, cCrtOp[S][c], res)
        /\ UNCHANGED <<cCrtOpToFinalize>>
  /\ cCrtOp' = [cCrtOp EXCEPT ![S][c] = <<>>]
  /\ cCrtOpReplies' = [cCrtOpReplies EXCEPT ![S][c] = {}]
  /\ UNCHANGED <<cMsgCounter, cState, cCrtOpConfirms, rVars, arRecord, aVisibility, gViewChangesNo>>

\* \* Client received a confirm
ClientReceiveConfirm(c) ==
  \E msg \in sentMsg[S]:
    /\ msg.type = "CONFIRM"
    /\ cCrtOpToFinalize[S][c] /= <<>>
    /\ msg.id = [cid |-> c, msgid |-> cMsgCounter[S][c]] \* reply to c's request for crt op
    /\ cCrtOpConfirms' = [cCrtOpConfirms EXCEPT ![S][c] = @ \cup 
                                           {[viewNumber |-> msg.v,
                                             res         |-> msg.res,
                                             src         |-> msg.src]}]
    /\ UNCHANGED <<cCrtOp, cCrtOpReplies, cCrtOpToFinalize, cMsgCounter,
                   cState, rVars, aVars, oVars>>


\* \* An operation is finalized by a client and result returned to the application
ClientFinalizeOp(c) ==
  /\ cCrtOpToFinalize[S][c] /= <<>>
  /\ \E Q \in Quorums:
     \* IR client received a quorum of confirms
     /\ \A r \in Q:
         \E reply \in cCrtOpConfirms[S][c]: reply.src = r
     /\ LET
           \* take the result in the biggest view number
           reply == CHOOSE reply \in cCrtOpConfirms[S][c]:
                                     ~ \E rep \in cCrtOpConfirms[S][c]:
                                            rep.viewNumber > reply.viewNumber
        IN
          /\ aSuccessful' = aSuccessful \cup
                                 {[mid |-> [cid |-> c,
                                            msgid |-> cMsgCounter[S][c]],
                                   op |-> cCrtOpToFinalize[S][c],
                                   res |-> reply.res]}
          /\ SuccessfulConsensusOp(c, S, cCrtOp[S][c], reply.res)  \* respond to app     
  /\ cCrtOpToFinalize' = [cCrtOpToFinalize EXCEPT ![S][c] = <<>>]
  /\ cCrtOpConfirms' = [cCrtOpConfirms EXCEPT ![S][c] = {}]
  /\ UNCHANGED <<rVars, cCrtOp, cCrtOpReplies,
                 cMsgCounter, cState, arRecord, aVisibility, oVars>>

\* \* Client fails and looses all data
ClientFail(c) ==
  /\ cState' = [cState EXCEPT ![S][c] = "FAILED"]
  /\ cMsgCounter' = [cMsgCounter EXCEPT ![S][c] = 0]
  /\ cCrtOp' = [cCrtOp EXCEPT ![S][c] = <<>>]
  /\ cCrtOpReplies' = [cCrtOpReplies EXCEPT ![S][c] = {}]
  /\ AppClientFail
  /\ UNCHANGED <<rVars, aVars, oVars>>

\* \* Client recovers
\* \* Not implemented yet
ClientRecover(c) == FALSE

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Replica Actions}} ^'                          *)
(***************************************************************************)

\* \* Replica sends a reply
ReplicaReceiveRequest(r) ==
  \E msg \in sentMsg[S]:
     /\ msg.type = "PROPOSE"
     /\ \* not already replied for this op
        ~ (\E rec \in rRecord[S][r]: rec.msgid = msg.id) 
     /\ \/ /\ msg.op.type = "Inconsistent"
           /\ Send([type |-> "REPLY",
                    id   |-> msg.id,
                    v    |-> rCrtView[S][r],
                    src  |-> r])
          /\ rRecord' = [rRecord EXCEPT ![S][r] =
                           @ \cup {[msgid |-> msg.id,
                                    op |-> msg.op,
                                    status |-> "TENTATIVE"]}]
        \/ /\ msg.op.type = "Consensus"
           /\ LET res == ExecConsensus(msg.op)
              IN
                /\ Send([type |-> "REPLY",
                         id   |-> msg.id,
                         v    |-> rCrtView[S][r],
                         res  |-> res,
                         src  |-> r])
                /\ rRecord' = [rRecord EXCEPT ![S][r] =
                                 @ \cup {[msgid |-> msg.id,
                                          op |-> msg.op,
                                          res |-> res,
                                          status |-> "TENTATIVE"]}]
    /\ UNCHANGED <<rState, rCrtView, rLastView, rViewOnDisk,
                   rViewReplies, rNonce, cVars, aVars, gViewChangesNo>>

\* \* Replica receives a message from an IR Client to finalize an op 
\* \* For inconsistent oprations the replica just
\* \* executes the operation.
ReplicaReceiveFinalize(r) ==
  \E msg \in sentMsg[S]:
     /\ msg.type = "FINALIZE"
     /\ msg.v >= rCrtView[S][r]
     /\ LET recs == {rec \in rRecord[S][r]: \* Must be only 1 record
                                     /\ rec.msgid = msg.id 
                                     /\ rec.op = msg.op}
        IN
          \/ /\ msg.op.type = "Inconsistent"
             /\ IF 
                  \* Replica knows of this op 
                  recs /= {}
                THEN
                  IF \A rec \in recs: rec.status /= "FINALIZED"
                  THEN ExecInconsistent(msg.op)
                  ELSE TRUE
                ELSE
                  \* Replica didn't hear of this op
                  ExecInconsistent(msg.op)
             /\ rRecord' = [rRecord EXCEPT ![S][r] = (@ \ recs) \cup
                                                  {[msgid |-> msg.id,
                                                    op |-> msg.op,
                                                    status |-> "FINALIZED"]}]
             /\ UNCHANGED <<sentMsg>>
          \/ /\ msg.op.type = "Consensus"
             /\ rRecord' = [rRecord EXCEPT ![S][r] = (@ \ recs) \cup
                                                  {[msgid |-> msg.id,
                                                    op |-> msg.op,
                                                    res |-> msg.res,
                                                    status |-> "FINALIZED"]}]
             /\ Send([type |-> "CONFIRM",
                      v    |-> rCrtView[S][r],
                      id   |-> msg.id,
                      op   |-> msg.op,
                      res  |-> msg.res,
                      src  |-> r])
     /\ UNCHANGED <<rState, rCrtView, rLastView, rViewReplies, rViewOnDisk,
                    rNonce, cVars, aVars, gViewChangesNo>>


\* \* A recovering replica starts the view change procedure
ReplicaSendDoViewChange(r) ==
  /\ \/ /\ rState[S][r] = "NORMAL" \/ rState[S][r] = "VIEW-CHANGING"
        /\ rCrtView' = [rCrtView EXCEPT ![S][r] = @ + 1]
        /\ rViewOnDisk' = [rViewOnDisk EXCEPT ![S][r] = rCrtView[S][r] + 1]
        /\ rState' = [rState EXCEPT ![S][r] = "VIEW-CHANGING"]
        /\ Send([type |-> "DO-VIEW-CHANGE",
                 v    |-> rCrtView[S][r] + 1,
                 lv   |-> rLastView[S][r],
                 r    |-> rRecord[S][r],
                 src  |-> r,
                 dst  |-> Replicas])
     \/ /\ rState[S][r] = "FAILED"
        /\ rState' = [rState EXCEPT ![S][r] = "RECOVERING"]
        /\ rCrtView' = [rCrtView EXCEPT ![S][r] = rViewOnDisk[S][r]]
        /\ Send([type |-> "DO-VIEW-CHANGE",
                 v    |-> rViewOnDisk[S][r],
                 lv   |-> rLastView[S][r],
                 r    |-> rRecord[S][r],
                 src  |-> r,
                 dst  |-> Replicas \ {x \in Replicas: IsLeader(x, rViewOnDisk[S][r])}])
        /\ UNCHANGED <<rViewOnDisk>>
     \/ /\ rState[S][r] = "RECOVERING"
        /\ rCrtView' = [rCrtView EXCEPT ![S][r] = @ + 1]
        /\ Send([type |-> "DO-VIEW-CHANGE",
             v    |-> rCrtView[S][r] + 1,
             lv   |-> rLastView[S][r],
             r    |-> rRecord[S][r],
             src  |-> r,
             dst  |-> Replicas \ {x \in Replicas: IsLeader(x, rCrtView[S][r] + 1)}])
        /\ UNCHANGED <<rViewOnDisk, rState>>
  /\ UNCHANGED <<cVars, rLastView, rViewReplies, rRecord,
                   rNonce, aVars>>
  /\ gViewChangesNo[S] < max_vc \* BOUND on number of view changes
  /\ gViewChangesNo' = [gViewChangesNo EXCEPT ![S] = @ + 1]

\* \* Replica received DO-VIEW-CHANGE message
ReplicaReceiveDoViewChange(r) ==
  /\ \E msg \in sentMsg[S]:
       /\ msg.type = "DO-VIEW-CHANGE"
       /\ r \in msg.dst
       /\ \/ /\ rState[S][r] = "NORMAL"
             /\ msg.v > rCrtView[S][r]
          \/ /\ rState[S][r] = "VIEW-CHANGING"
             /\ msg.v >= rCrtView[S][r]
       /\ rState' = [rState EXCEPT ![S][r] = "VIEW-CHANGING"]
       \* keep only the one with the higher view (v)
       /\ \/ /\ IsLeader(r, msg.v)
             /\  LET
                   existingRecord == {x \in rViewReplies[S][r]:
                                   /\ x.type = "do-view-change"
                                  /\ x.src = msg.src} \* should only be one item in set
                 IN
                   IF \A x \in existingRecord: x.v < msg.v
                   THEN rViewReplies' = [rViewReplies EXCEPT ![S][r] =
                                        (@ \ existingRecord) \cup
                                          {[type       |-> "do-view-change",
                                            v          |-> msg.v,
                                            lv         |-> msg.lv,
                                            r          |-> msg.r,
                                            src        |-> msg.src]}]
                   ELSE FALSE
          \/ UNCHANGED <<rViewReplies>>
       /\ rCrtView' = [rCrtView EXCEPT ![S][r] = msg.v]
       /\ rViewOnDisk' = [rViewOnDisk EXCEPT ![S][r] = msg.v]
       /\ Send([type |-> "DO-VIEW-CHANGE",
             v    |-> msg.v,
             lv   |-> rLastView[S][r],
             r    |-> rRecord[S][r],
             src  |-> r,
             dst  |-> Replicas])
  /\ UNCHANGED <<cVars, rLastView, rRecord, rNonce,
                 aVars, gViewChangesNo>>

\* Note: Assume one reply for view change per replica in Q
\* (in ReplicaReceiveDoViewChange we keep only the most recent reply)
ReplicaSendStartView(r) ==
  /\ \E Q \in Quorums:
    /\ \A r1 \in Q:
      /\ \A r2 \in Q: \E rr, pr \in rViewReplies[S][r]:
                                  /\ rr.type = "do-view-change"
                                  /\ pr.type = "do-view-change"
                                  /\ rr.src = r1
                                  /\ pr.src = r2
                                  /\ rr.v = pr.v
                                  /\ rr.v >= rCrtView[S][r]
    \* received at a least a quorum of replies
    /\ LET
           A ==
             \* set of all do-view-change replies from Q,
             {x \in rViewReplies[S][r]: /\ x.src \in Q
                                        /\ x.type = "do-view-change"}

           B ==
             \* keep only the replies from the maximum view
             {x \in A: \A y \in A: y.lv <= x.lv}

           C ==
             \* set of all records received in replies in B
             UNION {x.r: x \in B}

           recoveredConsensusOps_R ==
           \* any finalized consensus operation (in at least one record,
           \* in the maximum latest view)
           {[msgid |-> y.msgid, op |-> y.op, res |-> y.res]: y \in
             {x \in C:
                /\ x.op.type = "Consensus"
                /\ x.status = "FINALIZED"}}

           recoveredConsensusOps_d ==
           \* any consensus operation found in at least a majority of a Quorum
           {[msgid |-> y.msgid, op |-> y.op, res |-> y.res]: y \in
             {x \in C:
               /\ x.op.type = "Consensus"
               /\ x.status = "TENTATIVE"
               /\ \E P \in SuperQuorums:
                     \A replica \in Q \cap P:
                       \E reply \in B:
                         /\ reply.src = replica
                         /\ x \in reply.r}} \ recoveredConsensusOps_R

           recoveredConsensusOps_u ==
           \* the rest of consensus ops found in at least one record
           \* (discard the result)
           {[msgid |-> z.msgid, op |-> z.op]: z \in
             (({[msgid |-> y.msgid, op |-> y.op, res |-> y.res]: y \in
               {x \in C: x.op.type = "Consensus"}}
                \ recoveredConsensusOps_d) \ recoveredConsensusOps_R)}

           recoveredInconsistentOps_R ==
           \* any inconsistent operation found in any received record
           {[msgid |-> y.msgid, op |-> y.op]: y \in
             {x \in C: x.op.type = "Inconsistent"}}
           
           mergedRecordInconsistent ==
             {x \in Merge(recoveredConsensusOps_R
                     \cup recoveredInconsistentOps_R,
                   recoveredConsensusOps_d,
                   recoveredConsensusOps_u): x.op.type = "Inconsistent"}

           mergedRecordConsensus ==
             {x \in Merge(recoveredConsensusOps_R
                     \cup recoveredInconsistentOps_R,
                   recoveredConsensusOps_d,
                   recoveredConsensusOps_u): x.op.type = "Consensus"}

           masterRecord ==
             {[msgid |-> x.msgid,
               op |-> x.op,
               status |-> "FINALIZED"]:
                 x \in mergedRecordInconsistent}
           \cup
             {[msgid |-> x.msgid,
               op |-> x.op,
               res |-> x.res,
               status |-> "FINALIZED"]:
                 x \in mergedRecordConsensus}

           v_new ==
             \* the one decided by quorum Q
             CHOOSE v \in {x.v: x \in A}: TRUE
       IN
           /\ rRecord' = [rRecord EXCEPT ![S][r] = masterRecord]
           /\ Sync(masterRecord)
           /\ Send([type |-> "START-VIEW",
                    v    |-> v_new,
                    r    |-> masterRecord,
                    src  |-> r])
           /\ rCrtView' = [rCrtView EXCEPT ![S][r] = v_new]
           /\ rLastView' = [rLastView EXCEPT ![S][r] = v_new]
           \*/\ Assert(Cardinality(masterRecord) = 0, "Should fail - ReplicaSendStartView")
  /\ rState' = [rState EXCEPT ![S][r] = "NORMAL"]
  /\ rViewReplies' = [rViewReplies EXCEPT ![S][r] = {}]
  /\ UNCHANGED <<rNonce, rViewOnDisk, cVars, aVars, gViewChangesNo>>

\* \* A replica receives a start view message
ReplicaReceiveStartView(r) ==
  /\ \E msg \in sentMsg[S]:
    /\ msg.type = "START-VIEW"
    /\ \/ /\ rState[S][r] = "NORMAL"
          /\ msg.v > rCrtView[S][r]
       \/ /\ \/ rState[S][r] = "VIEW-CHANGING"
             \/ rState[S][r] = "RECOVERING"
          /\ msg.v >= rCrtView[S][r]
    /\ rCrtView' = [rCrtView EXCEPT ![S][r] = msg.v]
    /\ rLastView' = [rLastView EXCEPT ![S][r] = msg.v]
    /\ rRecord' = [rRecord EXCEPT ![S][r] = msg.r]
    /\ Sync(msg.r)
    /\ \* Check if the operations received in the master record
       \* must be added to the aSuccessful
       LET
         successfulOps == {x \in msg.r: \E Q \in Quorums:
                                          \A r1 \in Q:
                                            \/ x \in rRecord[S][r1]
                                            \/ x \in arRecord[S][r1]
                                            \/ r1 = r}
       IN
         aSuccessful' = aSuccessful \cup
                            {[mid |-> x.msgid,
                              op  |-> x.op,
                              res |-> x.res]:
                                x \in 
                                  {y \in successfulOps:
                                     y.op.type = "Consensus"}}
                            \cup
                            {[mid |-> x.msgid,
                              op  |-> x.op]:
                                x \in
                                  { y \in successfulOps:
                                      y.op.type = "Inconsistent"}}
    /\ rViewOnDisk' = [rViewOnDisk EXCEPT ![S][r] = msg.v + 1]
  /\ rState' = [rState EXCEPT ![S][r] = "NORMAL"]
  /\ rViewReplies' = [rViewReplies EXCEPT ![S][r] = {}]
  /\ UNCHANGED <<rNonce, cVars, arRecord, aVisibility, oVars>>

\* \* A replica fails and looses everything except the view number
\* \* The view number has been written to disk
ReplicaFail(r) ==
  /\ rState' = [rState EXCEPT ![S][r] = "FAILED"]
  /\ rRecord' = [rRecord EXCEPT ![S][r] = {}]
  /\ arRecord' = [arRecord EXCEPT ![S][r] = rRecord[S][r]]
                                              \* save record only for
                                              \* invariant purposes
  /\ rCrtView' = [rCrtView EXCEPT ![S][r] = 0]
  /\ rLastView' = [rLastView EXCEPT ![S][r] = 0]
  /\ rViewReplies' = [rViewReplies EXCEPT ![S][r] = {}]
  /\ UNCHANGED <<rViewOnDisk, rNonce, cVars, aSuccessful, aVisibility, oVars>>
  /\ \* We assume less than f replicas fail simultaneously
     Cardinality({re \in Replicas:
                           \/ rState[S][re] = "FAILED"
                           \/ rState[S][re] = "RECOVERING"}) < f

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{High-Level Actions}} ^'                       *)
(***************************************************************************)

ClientAction(c) ==
  \/ /\ cState[c] = "NORMAL"
     /\ \* \/ ClientRequest(c) \* some client tries to replicate commit an operation
        \/ ClientReceiveReply(c)  \* some client receives a reply from a replica
        \/ ClientReceiveConfirm(c) \* some client receives a confirm from a replica
        \* \/ ClientFail(c)     \* some client fails
        \/ ClientSendFinalize(c) \* an operation is successful at some client
        \/ ClientFinalizeOp(c) \* an operation was finalized at some client
  \/ /\ cState[c] = "FAILED"
     /\ \/ ClientRecover(c)

ReplicaAction(r) ==
  \/ /\ rState[S][r] = "NORMAL"
     /\ \/ ReplicaReceiveRequest(r) \* some replica sends a reply to a PROPOSE msg
        \/ ReplicaReceiveFinalize(r)
        \/ ReplicaSendDoViewChange(r)
        \/ ReplicaReceiveDoViewChange(r)
        \/ ReplicaReceiveStartView(r)
        \/ ReplicaFail(r)       \* some replica fails
  \/ /\ rState[S][r] = "FAILED"
     /\ \/ ReplicaSendDoViewChange(r) \* start view-change protocol
  \/ /\ rState[S][r] = "RECOVERING"
     /\ \/ ReplicaSendDoViewChange(r)\* re-start view-change protocol (assume a
                                     \* timeout and still no response from the new leader)
        \/ ReplicaReceiveStartView(r)
  \/ /\ rState[S][r] = "VIEW-CHANGING"
     /\ \/ ReplicaSendDoViewChange(r)
        \/ ReplicaReceiveDoViewChange(r)
        \/ ReplicaSendStartView(r)
        \/ ReplicaReceiveStartView(r)
        \/ ReplicaFail(r)

Next ==
     \/ \E c \in Clients: ClientAction(c)
     \/ \E r \in Replicas: ReplicaAction(r)
     \*\/ \* Avoid deadlock by termination
     \*  (\A i \in 1..Cardinality(Replicas): rLastView[S][i] = max_vc) \/ UNCHANGED <<vars>>

Spec == Init /\ [] [Next]_vars

FaultTolerance ==
  /\ \A successfulOp \in aSuccessful, Q \in Quorums:
         (\A r \in Q: rState[S][r] = "NORMAL" \/ rState[S][r] = "VIEW-CHANGING")
      => (\E p \in Q: \E rec \in rRecord[S][p]:
            /\ successfulOp.mid = rec.msgid
            /\ successfulOp.op = rec.op)  \* Not necessarily same result


=============================================================================
\* Modification History
\* Last modified Fri Aug 28 10:58:02 PDT 2015 by aaasz
\* Created Fri Dec 12 17:42:14 PST 2014 by aaasz
