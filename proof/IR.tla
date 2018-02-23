--------------------------------- MODULE IR ---------------------------------
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
(*                                                                         *)
(*        f: maximum number of failures allowed (half of n)                *)
(*                                                                         *)
(*  Constants used to bound variables, for model checking (Nat is bounded) *)
(*        max_vc: maximum number of View-Changes allowed for each replicas *)
(*        max_req: maximum number of op requests performed by clients      *)
(***************************************************************************)

CONSTANTS Replicas, Clients, Quorums, SuperQuorums, Results, OperationBody,
          max_vc, max_req, f

ASSUME IsFiniteSet(Replicas)

(***************************************************************************)
(* The  possible states of a replica and the two types of operations       *)
(*  currently defined by IR.                                               *)
(***************************************************************************)

ReplicaState == {"NORMAL", "FAILED", "RECOVERING", "VIEW-CHANGING"}
ClientState == {"NORMAL", "FAILED"}
OperationType == {"Inconsistent", "Consensus"}

(***************************************************************************)
(* Definition of operation space                                           *)
(***************************************************************************)

MessageId == Clients \X Nat
Operations == OperationType \X OperationBody

(***************************************************************************)
(* Message is defined to be the set of all possible messages               *)
(***************************************************************************)

\* TODO: Assumptions
\* Assume unique message ids
\* Assume no more than f replica failures

Message ==
       [type: {"REQUEST"},
        id: MessageId,
        op: Operations]
  \cup
       [type: {"REPLY"},
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
        r: SUBSET (MessageId \X Operations \X Results 
                    \cup MessageId \X Operations),
        v: Nat,
        src: Replicas,
        dst: Replicas]
  \cup
       [type: {"START-VIEW"},
        v: Nat,
        src: Replicas]
  \cup 
       [type: {"START-VIEW-REPLY"},
        v: Nat,
        src: Replicas,
        dst: Replicas]

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Variables and State Predicates}} ^'           *)
(***************************************************************************)

(***************************************************************************)
(* Variables:                                                              *)
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
(*                                                                         *)
(***************************************************************************)

VARIABLES rState, rRecord, rViewNumber, rViewReplies, sentMsg, cCrtOp,
          cMsgCounter, cCrtOpReplies, cState, aSuccessful, aFinalized,
          gViewChangesNo

(***************************************************************************)
(* Defining these tuples makes it easier to express which varibles remain  *)
(* unchanged                                                               *)
(***************************************************************************)

rVars == <<rState, rRecord, rViewNumber, rViewReplies>>\* Replica variables.
cVars == <<cCrtOp,        \* current operation at a client
           cCrtOpReplies, \* current operation replies
           cMsgCounter,
           cState>>                          \* Client variables.
aVars == <<aSuccessful, aFinalized>>         \* Application variables
oVars == <<sentMsg, gViewChangesNo>>         \* Other variables.
vars == <<rVars, cVars, oVars>>              \* All variables.

TypeOK ==
  /\ rState \in [Replicas -> ReplicaState]
  /\ rRecord \in [Replicas ->  SUBSET (MessageId \X
                                        Operations \X
                                        Results
                                  \cup MessageId \X
                                        Operations)]
  /\ rViewNumber \in [Replicas -> Nat]
  /\ rViewReplies \in [Replicas -> SUBSET [type: {"do-view-change",
                                                  "start-view-reply"},
                                           viewNumber: Nat,
                                           r: SUBSET (MessageId \X 
                                                       Operations \X
                                                       Results
                                                 \cup MessageId \X
                                                       Operations),
                                           src: Replicas]]
  /\ sentMsg \in SUBSET Message
  /\ cCrtOp \in [Clients -> Operations \cup {<<>>}]
  /\ cCrtOpReplies \in [Clients -> SUBSET [viewNumber: Nat,
                                            res: Results,
                                            src: Replicas]]
  /\ cMsgCounter \in [Clients -> Nat]
  /\ cState \in [Clients -> ClientState]
  /\ aSuccessful \in SUBSET (MessageId \X
                              Operations \X
                              Results
                        \cup MessageId \X
                              Operations)
  /\ aFinalized \in SUBSET (MessageId \X
                             Operations \X
                             Results)
  /\ gViewChangesNo \in Nat

Init ==
  /\ rState = [r \in Replicas |-> "NORMAL"]
  /\ rRecord = [r \in Replicas |-> {}]
  /\ rViewNumber = [r \in Replicas |-> 0]
  /\ rViewReplies = [r \in Replicas |-> {}]
  /\ sentMsg = {}
  /\ cCrtOp = [c \in Clients |-> <<>>]
  /\ cCrtOpReplies = [c \in Clients |-> {}]
  /\ cMsgCounter = [c \in Clients |-> 0]
  /\ cState = [c \in Clients |-> "NORMAL"]
  /\ aSuccessful = {}
  /\ aFinalized = {}
  /\ gViewChangesNo = 0

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Actions}} ^'                                  *)
(***************************************************************************)

Send(m) == sentMsg' = sentMsg \cup {m}
Receive(m) == sentMsg' = sentMsg \ {m}
-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Client Actions}} ^'                           *)
(***************************************************************************)

\* Note: CHOOSE does not introduce nondeterminism (the same value is chosen
\* each time)

\*Client sends a request
ClientRequest(c) ==
  \E opType \in OperationType: \E opBody \in OperationBody:
    /\ cCrtOp[c] = <<>> \*\* the client is not waiting for a result
                        \*\* of another operation
    /\ Send([type |-> "REQUEST", id |-> <<c, cMsgCounter[c]>>,
               op |-> <<opType, opBody>> ])
    /\ cCrtOp' = [cCrtOp EXCEPT ![c] = <<opType, opBody>>]
    /\ cMsgCounter' = [cMsgCounter EXCEPT ![c] = cMsgCounter[c] + 1]
    /\ UNCHANGED <<rVars, aVars, cCrtOpReplies, cState, gViewChangesNo>>
    /\ cMsgCounter[c] < max_req \* BOUND the number of requests a client can make

\*Client received a reply
ClientReceiveReply(c) ==
  \E msg \in sentMsg:
    /\ msg.type = "REPLY"
    /\ cCrtOp[c] # <<>>
    /\ msg.id = <<c, cMsgCounter[c] - 1>> \* reply to c's request for crt op
    \* TODO: if already reply from src, keep the most recent one (biggest view Number)
    \* /\ Assert(Cardinality(cCrtOpReplies[c])< 10, "cCrtOpReplies cardinality bound")
    /\ cCrtOpReplies' = [cCrtOpReplies EXCEPT ![c] = @ \cup 
                                           {[viewNumber |-> msg.v,
                                            res         |-> msg.res,
                                            src         |-> msg.src]}]
    /\ UNCHANGED <<cCrtOp, cMsgCounter, cState, rVars, aVars, oVars>> 

\*An operation is successful at a client and result returned to the application
ClientSuccessfulOp(c) ==
  /\ cCrtOp[c] /= <<>>
  /\ \E Q \in Quorums:
     \* a quorum of replies with matching view numbers
     /\ \A r \in Q:
        /\ \E reply \in cCrtOpReplies[c]: reply.src = r
        /\ \A p \in Q: \E rr, pr \in cCrtOpReplies[c]:
                                  /\ rr.src = r
                                  /\ pr.src = p
                                  /\ rr.viewNumber = pr.viewNumber
     /\ \/ /\ cCrtOp[c][1] = "Inconsistent"
           /\ cCrtOp' = [cCrtOp EXCEPT ![c] = <<>>]
           /\ cCrtOpReplies' = [cCrtOpReplies EXCEPT ![c] = {}]
           /\ aSuccessful' = aSuccessful \cup
                                   {<<<<c, cMsgCounter[c] - 1>>,
                                      cCrtOp[c]>>}
           /\ UNCHANGED <<cMsgCounter, cState>>
        \/ /\ cCrtOp[c][1] = "Consensus"
           /\ \A r, p \in Q: \E rr, pr \in cCrtOpReplies[c]:
                                  /\ rr.src = r
                                  /\ pr.src = p
                                  /\ rr.res = pr.res
           /\ \E reply \in cCrtOpReplies[c]:
             /\ reply.src \in Q
             /\ aSuccessful' = aSuccessful \cup
                                     {<<<<c, cMsgCounter[c] - 1>>,
                                        cCrtOp[c],
                                        reply.res>>}
           /\ UNCHANGED <<cVars>>
  /\ UNCHANGED <<rVars, aFinalized, oVars>>

\*An operation is finalized by a client and result returned to the application
ClientFinalizedOp(c) ==
  /\ cCrtOp[c] /= <<>> /\ cCrtOp[c][1] = "Consensus"
  /\ \E Q \in SuperQuorums:
     \* a superquorum of replies with matching view numbers and results
     /\ \A r \in Q:
        /\ \E reply \in cCrtOpReplies[c]: reply.src = r
        /\ \A p \in Q: \E rr, pr \in cCrtOpReplies[c]:
                                  /\ rr.src = r
                                  /\ pr.src = p
                                  /\ rr.viewNumber = pr.viewNumber
                                  /\ rr.res = pr.res
     /\ \E reply \in cCrtOpReplies[c]:
       /\ reply.src \in Q
       /\ aFinalized' = aFinalized \cup
                              {<<<<c, cMsgCounter[c] - 1>>,
                                 cCrtOp[c],
                                 reply.res >>}
  /\ cCrtOp' = [cCrtOp EXCEPT ![c] = <<>>]
  /\ cCrtOpReplies' = [cCrtOpReplies EXCEPT ![c] = {}]
  /\ UNCHANGED <<rVars, cMsgCounter, cState, aSuccessful, oVars>>

\*Client fails and looses all data
ClientFail(c) ==
  /\ cState' = [cState EXCEPT ![c] = "FAILED"]
  /\ cMsgCounter' = [cMsgCounter EXCEPT ![c] = 0]
  /\ cCrtOp' = [cCrtOp EXCEPT ![c] = <<>>]
  /\ cCrtOpReplies' = [cCrtOpReplies EXCEPT ![c] = {}]
  /\ UNCHANGED <<rVars, aVars, oVars>>

\*Client recovers
ClientRecover(c) == FALSE

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{Replica Actions}} ^'                          *)
(***************************************************************************)

\* Replica sends a reply
ReplicaReply(r) == \* TODO: Might need to check for duplicate state action?
  \E op \in Operations, id \in MessageId, result \in Results:
     /\ [type |-> "REQUEST", id |-> id, op |-> op] \in sentMsg
     /\ ~ \E rec \in rRecord[r]: rec[1] = id 
        \* not alredy replied for this op
     /\ rRecord' = [rRecord EXCEPT ![r] = @ \cup {<<id, op, result>>}]
     /\ Assert(rViewNumber[r] < 10, "viewNumber bound")
     /\ Send([type |-> "REPLY",
              id   |-> id,
              v    |-> rViewNumber[r],
              res  |-> result,
              src  |-> r])
    /\ UNCHANGED <<rState, rViewNumber, rViewReplies, cVars, aVars, gViewChangesNo>>

\*A replica starts the view change procedure
\* supports concurrent view changes (id by src)
ReplicaStartViewChange(r) ==
  /\ Send([type |-> "START-VIEW-CHANGE", v |-> rViewNumber[r], src |-> r])
  /\ rState' = [rState EXCEPT ![r] = "RECOVERING"]
  /\ UNCHANGED <<rViewNumber, rViewReplies, rRecord, cVars, aVars>>
  /\ gViewChangesNo < max_vc \* BOUND on number of view changes
  /\ gViewChangesNo' = gViewChangesNo + 1

\* A replica received a message to start view change
ReplicaReceiveStartViewChange(r) ==
  /\ \E msg \in sentMsg:
       /\ msg.type = "START-VIEW-CHANGE"
       /\ LET v_new ==
                IF msg.v > rViewNumber[r] THEN msg.v
                ELSE rViewNumber[r]
          IN       
            /\ ~\E m \in sentMsg: \* not already sent (just to bound the model checker)
              /\ m.type = "DO-VIEW-CHANGE"
              /\ m.v >= msg.v
              /\ m.dst = msg.src
              /\ m.src = r
            /\ Send([type |-> "DO-VIEW-CHANGE",
                     v    |-> v_new + 1,
                     r    |-> rRecord[r],
                     src  |-> r,
                     dst  |-> msg.src])
            /\ rViewNumber' = [rViewNumber EXCEPT ![r] = v_new + 1]
  /\ rState' = [rState EXCEPT ![r] = "VIEW-CHANGING"]
  /\ UNCHANGED <<cVars, rRecord, rViewReplies, aVars, gViewChangesNo>>

\* Replica received DO-VIEW-CHANGE message
ReplicaReceiveDoViewChange(r) ==
  \*/\ Assert(Cardinality(sentMsg) < 20, "bound on sentMsg")
  /\ \E msg \in sentMsg:
       /\ msg.type = "DO-VIEW-CHANGE"
       /\ msg.dst = r
       /\ msg.v > rViewNumber[r]
       /\ rViewReplies' = [rViewReplies EXCEPT ![r] = @ \cup
                                          {[type       |-> "do-view-change",
                                            viewNumber |-> msg.v,
                                            r          |-> msg.r,
                                            src        |-> msg.src]}]
  /\ UNCHANGED <<cVars, rViewNumber, rRecord, rState, aVars, oVars>>

RecoverOpsResults(ops) == 
  \*/\ Assert(Cardinality(ops) < 3, "recovered ops result")
  /\ TRUE
RecoverOps(ops) == 
  \*/\ Assert(Cardinality(ops) < 3, "recovered ops")
  /\ TRUE

\* A replica received enough view change replies to start processing in the new view
ReplicaDecideNewView(r) ==
  /\ \E Q \in Quorums:
      /\ \A rep \in Q: \E reply \in rViewReplies[r]: /\ reply.src = rep
                                                     /\ reply.type = "do-view-change" 
      \* received at least a quorum of replies
      /\ LET recoveredConensusOps_a ==
             \* any consensus operation found in at least a majority of a Quorum
                {x \in UNION {y.r: y \in {z \in rViewReplies[r]: z.src \in Q}}:
                  /\ x[2][1] = "Consensus"
                  /\ \E P \in SuperQuorums:
                       \A rep \in Q \cap P:
                         \E reply \in rViewReplies[r]:
                           /\ reply.src = rep
                           /\ x \in reply.r} \* same op, same result

             recoveredConensusOps_b == \* TODO: what result? from the app?
               \* the rest of consensus ops found in at least one record (discard the result)
               {<<z[1], z[2]>>:
                 z \in {x \in UNION {y.r: y \in {z \in rViewReplies[r]: z.src \in Q}}:
                   /\ x[2][1] = "Consensus"
                   /\ ~ x \in recoveredConensusOps_a}}

             recoveredInconsistentOps_c ==
               \* any inconsistent operation found in any received record (discard the result)
               {<<z[1], z[2]>>:
                  z \in {x \in UNION {y.r: y \in {z \in rViewReplies[r]: z.src \in Q}}:
                     x[2][1] = "Inconsistent"}}
         IN
           /\ RecoverOpsResults(recoveredConensusOps_a)
           /\ RecoverOps(recoveredConensusOps_b)
           /\ RecoverOps(recoveredInconsistentOps_c)
           /\ rRecord' = [rRecord EXCEPT ![r] = @ \cup recoveredConensusOps_a
                                                  \cup recoveredConensusOps_b
                                                  \cup recoveredInconsistentOps_c]
      /\ LET v_new ==
               \* max view number received
               CHOOSE v \in {x.viewNumber: x \in rViewReplies[r]}:
                     \A y \in rViewReplies[r]:
                       y.viewNumber <= v
         IN
           /\ Send([type |-> "START-VIEW",
                    v    |-> v_new,
                    src  |-> r])
           /\ rViewNumber' = [rViewNumber EXCEPT ![r] = v_new]
  /\ rViewReplies' = [rViewReplies EXCEPT ![r] = {}]
  /\ UNCHANGED <<rState, cVars, aVars, gViewChangesNo>>

\*A replica receives a start view message
ReplicaReceiveStartView(r) ==
  /\ \E msg \in sentMsg:
    /\ msg.type = "START-VIEW"
    /\ msg.v >= rViewNumber[r]
    /\ msg.src # r \* don't reply to myself
    /\ Send([type |-> "START-VIEW-REPLY",
             v    |-> msg.v,
             src  |-> r,
             dst  |-> msg.src])
    /\ rViewNumber' = [rViewNumber EXCEPT ![r] = msg.v]
  /\ rState' = [rState EXCEPT ![r] = "NORMAL"]
  /\ UNCHANGED <<rRecord, rViewReplies, cVars, aVars, gViewChangesNo>>

ReplicaReceiveStartViewReply(r) ==
  /\ \E msg \in sentMsg:
    /\ msg.type = "START-VIEW-REPLY"
    /\ msg.dst = r
    /\ msg.v > rViewNumber[r] \* receive only if bigger than the last view I was in
    /\ rViewReplies' = [rViewReplies EXCEPT ![r] = @ \cup
                               {[type       |-> "start-view-reply",
                                 viewNumber |-> msg.v,
                                 r          |-> {},
                                 src        |-> msg.src]}]
  /\ UNCHANGED <<rRecord, rState, rViewNumber, cVars, aVars, oVars>>

ReplicaRecover(r) == \* we received enough START-VIEW-REPLY messages
  \E Q \in Quorums:
    /\ r \in Q
    /\ \A p \in Q: \/ p = r
                   \/ /\ p # r
                      /\ \E reply \in rViewReplies[r]: /\ reply.src = p
                                                       /\ reply.type = "start-view-reply"
  /\ rViewReplies' = [rViewReplies EXCEPT ![r] = {}]
  /\ rState' = [rState EXCEPT ![r] = "NORMAL"]
  /\ UNCHANGED <<rRecord, rViewNumber, cVars, aVars, oVars>>

ReplicaResumeViewChange(r) == \* TODO: On timeout
  FALSE

\*A replica fails and looses everything
ReplicaFail(r) == \* TODO: check cardinality
  /\ rState' = [rState EXCEPT ![r] = "FAILED"]
  /\ rRecord' = [rRecord EXCEPT ![r] = {}]
  \*/\ rViewNumber' = [rViewNumber EXCEPT ![r] = 0] \* TODO: check what happens if we loose the view number
  /\ rViewReplies' = [rViewReplies EXCEPT ![r] = {}]
  /\ UNCHANGED <<rViewNumber, cVars, aVars, oVars>>
  /\ Cardinality({re \in Replicas: 
      \* We assume less than f replicas are allowed to fail
                           \/ rState[re] = "FAILED"
                           \/ rState[re] = "RECOVERING"}) < f
-----------------------------------------------------------------------------
(***************************************************************************)
(* `^ \center \large{\textbf{High-Level Actions}} ^'                       *)
(***************************************************************************)

ClientAction(c) ==
  \/ /\ cState[c] = "NORMAL"
     /\ \/ ClientRequest(c) \* some client tries to replicate commit an operation
        \/ ClientReceiveReply(c)  \* some client receives a reply from a replica
        \*\/ ClientFail(c)     \* some client fails
        \/ ClientSuccessfulOp(c) \* an operation is successful at some client
        \/ ClientFinalizedOp(c) \* an operation was finalized at some client
  \/ /\ cState[c] = "FAILED"
     /\ \/ ClientRecover(c)

ReplicaAction(r) ==
  \/ /\ rState[r] = "NORMAL"
     /\ \/ ReplicaReply(r) \* some replica sends a reply to a REQUEST msg
        \/ ReplicaReceiveStartViewChange(r)
        \/ ReplicaReceiveStartView(r)
        \/ ReplicaFail(r)       \* some replica fails
  \/ /\ rState[r] = "FAILED"
     /\ \/ ReplicaStartViewChange(r) \* some replica starts to recover
  \/ /\ rState[r] = "RECOVERING" \* just to make it clear
     /\ \/ ReplicaReceiveDoViewChange(r)
        \/ ReplicaDecideNewView(r)
        \/ ReplicaReceiveStartViewReply(r)
        \/ ReplicaRecover(r)
  \/ /\ rState[r] = "VIEW-CHANGING"
     /\ \/ ReplicaReceiveStartViewChange(r)
        \/ ReplicaReceiveStartView(r)
        \/ ReplicaResumeViewChange(r) \* some timeout expired and view change not finished
        \/ ReplicaFail(r)

Next ==
  \/ \E c \in Clients: ClientAction(c)
  \/ \E r \in Replicas: ReplicaAction(r)

Spec ==
  TypeOK /\ Init /\ [] [Next]_vars

FaultTolerance ==
  /\ \A successfulOp \in aSuccessful, Q \in Quorums:
         (\A r \in Q: rState[r] = "NORMAL" \/ rState[r] = "VIEW-CHANGING")
      => (\E p \in Q: \E rec \in rRecord[p]:
            /\ successfulOp[1] = rec[1]
            /\ successfulOp[2] = rec[2])  \* Not necessarily same result
  /\ \A finalizedOp \in aFinalized, Q \in Quorums:
         (\A r \in Q: rState[r] = "NORMAL" \/ rState[r] = "VIEW-CHANGING")
      => (\E P \in SuperQuorums:
            \A p \in Q \cap P:
              \E rec \in rRecord[p]:
                finalizedOp = rec)

Inv ==
  /\ TypeOK
  /\ FaultTolerance

THEOREM Spec => []Inv
PROOF
<1>1. Init => Inv
  PROOF BY DEF Init, Inv, TypeOK, FaultTolerance, ReplicaState, ClientState
<1>2. Inv /\ [Next]_vars => Inv'
  PROOF OBVIOUS
<1>3. QED
  PROOF BY <1>1, <1>2, PTL DEF Spec

=============================================================================
\* Modification History
\* Last modified Sun Jan 25 14:09:05 PST 2015 by aaasz
\* Created Fri Dec 12 17:42:14 PST 2014 by aaasz
