------------------------ MODULE IR_consensus ------------

(*
This is a TLA+ specification of the Inconsistent Replication algorithm. (And a mechanically-checked proof of its correctness using TLAPS)
*)

EXTENDS FiniteSets, Naturals, TLC, TLAPS
----------------------------------------------------------
(****************************************)
(*Constants*)
(****************************************)
(*
Constant parameters: Replicas: the set of all replicas (Replica IDs)

Clients: the set of all clients (Client IDs)

Quorums: the set of all quorums

SuperQuorums: the set of all super quorums

Results: the set of all possible result types

OperationBody: the set of all possible operation bodies (with arguments, etc. - can be infinite)

S : shard id of the shard Replicas constitute

f : maximum number of failures allowed (half of n)

Constants used to bound variables, for model checking (Nat is bounded)

max_vc: maximum number of View-Changes allowed for each replicas

max_req: maximum number of op requests performed by clients
*)

CONSTANTS Replicas, Clients, Quorums,
   SuperQuorums, Results, OpBody,
   AppClientFail, AppReplicaFail,
   SuccessfulInconsistentOp(_), SuccessfulConsensusOp(_,_),
   Merge(_,_),
   Sync(_),
   ExecInconsistent(_),
   ExecConsensus(_),
   Decide(_),
   f,
   S, Shards, S, (* = shard id *)
   max_vc, max_req

ASSUME IsFiniteSet(Replicas)

ASSUME QuorumAssumption ==
   /\ Quorums \subseteq SUBSET Replicas
   /\  SuperQuorums \subseteq SUBSET Replicas
   /\  \A Q1, Q2 \in Quorums : Q1 \cap Q2 /=  {}
   /\  \A Q \in Quorums, R1, R2 \in SuperQuorums : Q \cap R1 \cap R2 /= {}

ASSUME FailuresAssumption ==
\A Q \in Quorums : Cardinality(Q) > f

(* The possible states of a replica and the two types of operations currently defined by IR. *)

ReplicaState == {"NORMAL", "FAILED", "RECOVERING", "VIEW-CHANGING"}

ClientState == {"NORMAL", "FAILED"}

OpType == {"Inconsistent", "Consensus"}

OpStatus == {"TENTATIVE", "FINALIZED"}

(* Definition of operation space *)

MessageId == [cid : Clients, msgid : Nat]

Operations == [type : OpType, body : OpBody]

(*
Message is defined to be the set of all possible messages

TODO : Assumptions
ASSUME unique message ids
ASSUME no more than f replica failures

We use shart to specify for what shard this message was
(we share the variables)

*)

Message ==
     [type : {"REQUEST"},
      id : MessageId,
      op : Operations]
\cup [type : {"REPLY"}, (*reply no result*)
      id : MessageId,
      v : Nat,
      src : Replicas]
\cup 
     [type : {"REPLY"}, (*reply with result*)
      id : MessageId,
      v : Nat,
      res : Results,
      src : Replicas]
     (* v = view num. *)
\cup 
     [type : {"START-VIEW-CHANGE"},
      v : Nat,
      src : Replicas]
\cup 
     [type : {"DO-VIEW-CHANGE"},
      r : SUBSET ([msgid : MessageId,
      op : Operations,
      res : Results]
\cup
     [msgid : MessageId,
      op : Operations]),
      v : Nat,
      src : Replicas,
      dst : Replicas]
\cup 
     [type : {"START-VIEW"},
      v : Nat,
      src : Replicas]
\cup 
     [type : {"START-VIEW-REPLY"},
      v : Nat,
      src : Replicas,
      dst : Replicas]
\cup 
     [type : {"FINALIZE"}, (* finalize with no result *)
      id : MessageId,
      op : Operations,
      res : Results]
\cup 
     [type : {"FINALIZE"}, (* finalize with result *)
      id : MessageId,
      op : Operations,
      res : Results]
\cup
     [type : {"CONFIRM"},
      v : Nat,
      id : MessageId,
      op : Operations,
      res : Results,
      src : Replicas]

------------------------------------------------------
(****************************************)
(* Variables and State Predicates *)
(****************************************)

(*
Variables: 1. State at each replica:
rState = Denotes current replica state. Either:
- NORMAL (processing operations)
- VIEW-CHANGING (participating in recovery)
rRecord = Unordered set of operations and their results rViewNumber = current view
number
2. State of communication medium: sentMsg = sent (but not yet received) messages
3. State at client: cCurrentOperation = crt operation requested by the client
cMmessageCounter = the message I must use for
the next operation

*)

VARIABLES rState, rRecord, rViewNumber,
          rViewReplies, sentMsg, cCrtOp,
          cCrtOpToFinalize, cMsgCounter,
          cCrtOpReplies, cCrtOpConfirms,
          cState, aSuccessful, gViewChangesNo

(* Defining these tuples makes it easier to express which varibles remain unchanged *)

rVars == <<rState, rRecord, rViewNumber, rViewReplies>>  (* Replica variables. *)


cVars == <<cCrtOp, (* current operation at a client *)
cCrtOpToFinalize,
cCrtOpReplies, (* current operation replies *)
cCrtOpConfirms,
cMsgCounter,
cState>> (*Client variables.*)

aVars == <<aSuccessful>> (*Application variables*)

oVars == <<sentMsg, gViewChangesNo>> (*Other variables.*)

vars == <<rVars, cVars, oVars>> (*All variables.*)

TypeOK ==
/\  rState[S] \in [Replicas -> ReplicaState]
/\  rRecord [S] \in [Replicas -> SUBSET (
            [ msgid : MessageId,
                 op : Operations,
                res : Results,
             status : OpStatus]
       \cup  [msgid : MessageId,
                 op : Operations,
             status : OpStatus])]
 /\  rViewNumber [S] \in [Replicas -> Nat]
 /\  rViewReplies[S] \in [Replicas -> SUBSET [type : {"do-view-change",
    "start-view-reply"},
    viewNumber : Nat,
    r : SUBSET ([msgid : MessageId,
                    op : Operations,
                   res : Results,
                status : OpStatus]
         \cup  [msgid : MessageId,
                   op : Operations,
               status : OpStatus]),
    src : Replicas]]
 /\  sentMsg [S] \in SUBSET Message
 /\  cCrtOp[S] \in [Clients -> Operations \cup  {<<>>}]
 /\  cCrtOpToFinalize \in [Clients -> Operations \cup  {<<>>}]
 /\  cCrtOpReplies[S] \in [Clients -> SUBSET ([viewNumber : Nat,
                      res : Results,
                      src : Replicas]
        \cup  [viewNumber : Nat,
                      src : Replicas])]
 /\  cCrtOpConfirms[S] \in [Clients -> SUBSET [viewNumber : Nat,
                       res : Results,
                       src : Replicas]]
 /\  cMsgCounter [S] \in [Clients -> Nat]
 /\  cState \in [Clients -> ClientState]
 /\  aSuccessful \in SUBSET ([mid : MessageId,
                               op : Operations,
                              res : Results]
                       \cup  [mid : MessageId,
                               op : Operations])
 /\  gViewChangesNo[S] \in Nat

Init ==
 /\  rState = [r \in Replicas |-> "NORMAL"]
 /\  rRecord = [r \in Replicas |-> {}]
 /\  rViewNumber = [r \in Replicas |-> 0]
 /\  rViewReplies = [r \in Replicas |-> {}]
 /\  sentMsg = {}
 /\  cCrtOp = [c \in Clients |-> <<>>]
 /\  cCrtOpToFinalize = [c \in Clients |-> <<>>]
 /\  cCrtOpReplies = [c \in Clients |-> {}]
 /\  cCrtOpConfirms = [c \in Clients |-> {}]
 /\  cMsgCounter = [c \in Clients |-> 0]
 /\  cState = [c \in Clients |-> "NORMAL"]
 /\  aSuccessful = {}
 /\  gViewChangesNo = 0

---------------------------------------------
(****************************************)
(* Actions *)
(****************************************)

Send(m) == sentMsg' = [sentMsg EXCEPT ! [S] = @ \cup  {m}]

-----------------------------------------------
(****************************************)
(* Client Actions *)
(****************************************)

(*
Note: choose does not introduce nondeterminism (the same value is chosen
each time)
Client sends a request
*)

ClientRequest(c, op) ==
 /\  cCrtOp[S][c] = <<>> (* the client is not waiting for a result 
of another operation *)
 /\  cCrtOpToFinalize[S][c] = <<>>
 /\  cMsgCounter' = [cMsgCounter EXCEPT ! [S][c] = @ + 1]
 /\  cCrtOp' = [cCrtOp EXCEPT ! [S][c] = op]
 /\  Send([type |-> "REQUEST",
             id |-> [cid |-> c, msgid |-> cMsgCounter [S][c] + 1],
             op |-> op])
 /\  UNCHANGED <<rVars, aVars, cCrtOpReplies, cCrtOpToFinalize,
                 cCrtOpConfirms, cState, gViewChangesNo>>
 /\  cMsgCounter [S][c] < max_req (*BOUND the number of requests a client can make*)


(*Client received a reply*)
ClientReceiveReply(c) ==
 \E msg \in sentMsg [S] :
    /\ msg.type = "REPLY"
    /\ cCrtOp[S][c] /= <<>>
    /\ msg.id = [cid |-> c, msgid |-> cMsgCounter [S][c]] (* reply to c's request for crt op *)

(* TODO : if already reply from src, keep the most recent one (biggest view Number) *)

    /\ Assert(Cardinality(cCrtOpReplies[c]) < 10, "cCrtOpReplies cardinality bound")
    /\  \/  /\  cCrtOp[S][c].type = "Inconsistent"
            /\  cCrtOpReplies' = [cCrtOpReplies EXCEPT ! [S][c] = @ \cup 
                                     {[viewNumber |-> msg.v,
                                              src |-> msg.src]}]
        \/  /\  cCrtOp[S][c].type = "Consensus"
            /\  cCrtOpReplies' = [cCrtOpReplies EXCEPT ! [S][c] = @ \cup 
                                       {[viewNumber |-> msg.v,
                                                res |-> msg.res,
                                                src |-> msg.src]}]
    /\  UNCHANGED <<cCrtOp, cCrtOpToFinalize, cCrtOpConfirms,
                     cMsgCounter, cState, rVars, aVars, oVars>>


(*"Helper" formulas*)

__matchingViewNumbers(Q, c) ==
(* a (super)quorum of replies with matching view numbers*)
 /\  \A  r \in Q :
         /\  \E  reply \in cCrtOpReplies[S][c]: reply.src = r
         /\  \A  p \in Q : \E  rr, pr \in cCrtOpReplies[S][c] :
                     /\  rr.src = r
                     /\  pr.src = p
                     /\  rr.viewNumber = pr.viewNumber

__matchingViewNumbersAndResults(Q, c) ==
(* a (super)quorum of replies with matching view numbers
and results *)
 /\  \A  r \in Q :
         /\  \E  reply \in cCrtOpReplies[S][c]: reply.src = r
         /\  \A  p \in Q : \E  rr, pr \in cCrtOpReplies[S][c] :
                             /\  rr.src = r
                             /\  pr.src = p
                             /\  rr.viewNumber = pr.viewNumber
                             /\  rr.res = pr.res

(*IR Client received enough responses to decide
what to do with the operation*)

ClientDecideOp(c) ==
 /\  cCrtOp[S][c] /= <<>>

 (* I. The IR Client got a simple quorum of replies *)
 /\  \/  \E Q \in Quorums :
          /\  \A  r \in Q :
                  \E  reply \in cCrtOpReplies[S][c] : reply.src = r
          /\  \/  /\  cCrtOp[S][c].type = "Inconsistent"
                  /\  __matchingViewNumbers(Q, c)
                  /\  aSuccessful' = aSuccessful \cup 
                      {[mid |-> [cid |-> c,
                               msgid |-> cMsgCounter [S][c]],
                                  op |-> cCrtOp[S][c]]}
                  /\  SuccessfulInconsistentOp(cCrtOp[S][c])
                  /\  Send([type |-> "FINALIZE",
                           id |-> [cid |-> c, msgid |-> cMsgCounter [S][c]],
                           op |-> cCrtOp[S][c]])
                  /\  UNCHANGED <<cCrtOpToFinalize>>
                  
              \/  /\  cCrtOp[S][c].type = "Consensus"
                  /\  LET res == IF __matchingViewNumbersAndResults(Q, c)
                                 THEN
                                   CHOOSE result \in
                         {res \in Results :
                      \E  reply \in cCrtOpReplies[S][c] :
                         /\  reply.src \in Q
                         /\  reply.res = res} : true
                                 ELSE
                                   Decide(cCrtOpReplies[S][c])
                      IN
                        /\  Send([type |-> "FINALIZE",
                           id |-> [cid |-> c, msgid |-> cMsgCounter [S][c]],
                           op |-> cCrtOp[S][c],
                           res |-> res])
                  /\  cCrtOpToFinalize' = [cCrtOp EXCEPT ! [S][c] = cCrtOp[S][c]]
                  /\  UNCHANGED <<aSuccessful>>
                  
(*II. The IR Client got super quorum of responses*)
     \/  \E SQ \in SuperQuorums :
          /\  \A  r \in SQ :
                  \E  reply \in cCrtOpReplies[S][c] : reply.src = r
          /\  cCrtOp[S][c].type = "Consensus" (*only care if consensus op*)
          /\  __matchingViewNumbersAndResults(SQ, c)
          /\  LET res == CHOOSE result \in
                  {res \in Results :
                    \E  reply \in cCrtOpReplies[S][c] :
                       /\  reply.src \in SQ
                       /\  reply.res = res} : true

              IN
                /\  Send([type |-> "FINALIZE",
                    id |-> [cid |-> c, msgid |-> cMsgCounter [S][c]],
                    op |-> cCrtOp[S][c],
                   res |-> res])
                /\  aSuccessful' = aSuccessful \cup 
                    {[mid |-> [cid |-> c,
                    msgid |-> cMsgCounter [S][c]],
                    op |-> cCrtOp[S][c],
                    res |-> res]}
                /\  SuccessfulConsensusOp(cCrtOp[S][c], res)
          /\  UNCHANGED <<cCrtOpToFinalize>>
 /\  cCrtOp' = [cCrtOp EXCEPT ! [S][c] = <<>>]
 /\  cCrtOpReplies' = [cCrtOpReplies EXCEPT ! [S][c] = {}]
 /\  UNCHANGED <<cMsgCounter, cState, cCrtOpConfirms, rVars, gViewChangesNo>>


(*Client received a confirm*)
ClientReceiveConfirm(c) ==
 \E msg \in sentMsg [S] :
    /\ msg.type = "CONFIRM"
    /\  cCrtOpToFinalize[S][c] /= <<>>
    /\ msg.id = [cid |-> c, msgid |-> cMsgCounter [S][c]] (* reply to c's request for crt op *)
    /\  cCrtOpConfirms' = [cCrtOpConfirms EXCEPT ! [S][c] = @ \cup 
        {[viewNumber |-> msg.v,
                 res |-> msg.res,
                 src |-> msg.src]}]
    /\  UNCHANGED <<cCrtOp, cCrtOpReplies, cCrtOpToFinalize, cMsgCounter, cState, rVars, aVars, oVars>>


(*An operation is finalized by a client and result returned to the application*)
ClientFinalizedOp(c) ==
 /\  cCrtOpToFinalize[S][c] /= <<>>
 /\  \E Q \in Quorums :
(*IR client received a quorum of responses*)
        /\  \A  r \in Q :
                \E  reply \in cCrtOpConfirms[S][c] : reply.src = r
        /\  LET
               (*take the result in the biggest view number*)

               reply == CHOOSE reply \in cCrtOpConfirms[S][c] :
                  ~\E  rep \in cCrtOpConfirms[S][c] :
                  rep.viewNumber > reply.viewNumber
            IN
              /\  aSuccessful' = aSuccessful \cup 
                  {[mid |-> [cid |-> c,
                           msgid |-> cMsgCounter [S][c]],
                           op |-> cCrtOpToFinalize[S][c],
                           res |-> reply.res]}
              /\  SuccessfulConsensusOp(cCrtOp[S][c], reply.res) (*respond to app*)
 /\  cCrtOpToFinalize' = [cCrtOpToFinalize EXCEPT ! [S][c] = <<>>]
 /\  cCrtOpConfirms' = [cCrtOpConfirms EXCEPT ! [S][c] = {}]
 /\  UNCHANGED <<rVars, cCrtOp, cCrtOpReplies, cMsgCounter, cState, oVars>>


(*Client fails and looses all data*)
ClientFail(c) ==
 /\  cState' = [cState EXCEPT ! [S][c] = "FAILED"]
 /\  cMsgCounter' = [cMsgCounter EXCEPT ! [S][c] = 0]
 /\  cCrtOp' = [cCrtOp EXCEPT ! [S][c] = <<>>]
 /\  cCrtOpReplies' = [cCrtOpReplies EXCEPT ! [S][c] = {}]
 /\ AppClientFail
 /\  UNCHANGED <<rVars, aVars, oVars>>


(*Client recovers*)
ClientRecover(c) == false

-----------------------------------------
(****************************************)
(* Replica Actions *)
(****************************************)

(* Replica sends a reply *)
ReplicaReceiveRequest(r) ==
 \E msg \in sentMsg [S] :
    /\ msg.type = "REQUEST"
    /\  ~\E  rec \in rRecord [S][r] : rec.msgid = msg.id
        (* not alredy replied for this op *)
    /\  \/  /\ msg.op.type = "Inconsistent"
            /\  Send([type |-> "REPLY",
                        id |-> msg.id,
                         v |-> rViewNumber [S][r],
                       src |-> r])

            /\  rRecord' = [rRecord EXCEPT ! [S][r] = @ \cup  {[msgid |-> msg.id,
                                                                   op |-> msg.op,
                                                               status |-> "TENTATIVE"]}]

        \/  /\ msg.op.type = "Consensus"
            /\  LET res == ExecConsensus(msg.op)
                IN
                  /\  Send([type |-> "REPLY",
                              id |-> msg.id,
                               v |-> rViewNumber [S][r],
                             res |-> res,
                             src |-> r])
                  /\  rRecord' = [rRecord EXCEPT ! [S][r] = @ \cup  {[msgid |-> msg.id,
                                                                         op |-> msg.op,
                                                                        res |-> res,
                                                                     status |-> "TENTATIVE"]}]
    /\  UNCHANGED <<rStaate, rViewNumber, rViewReplies, cVars, aVars, gViewChangesNo>>

(* Replica receive a message from an IR Client to finalize an op For inconsistent oprations the replica sends < CONFIRM > and executes the operation. *)


(* TODO : Write this more compact *)

ReplicaReceiveFinalize(r) ==
\E msg \in sentMsg [S] :
   /\ msg.type = "FINALIZE"
   /\  \/  /\ msg.op.type = "Inconsistent"
           /\  Send([type |-> "CONFIRM",
                        v |-> rViewNumber [S][r],
                       id |-> msg.id,
                       op |-> msg.op,
                      src |-> r])
           /\  \/  \E  rec \in rRecord [S][r] :
                       /\  rec.msgid = msg.id
                       /\  rec.op = msg.op (*Replica knows of this op*)
                       /\  IF rec.status /= "FINALIZED"
                           THEN ExecInconsistent(msg.op)
                           ELSE true
                       /\  rRecord' = [rRecord EXCEPT ! [S][r] = (@ \ {rec}) \cup {[msgid |-> msg.id,
                                                                                       op |-> msg.op,
                                                                                   status |-> "FINALIZED"]}]
               \/  /\  ~\E  rec \in rRecord [S][r] : (* Replica didn't hear of this op *)
                       /\  rec.msgid = msg.id
                       /\  rec.op = msg.op
                   /\  rRecord' = [rRecord EXCEPT ! [S][r] = @ \cup  {[msgid |-> msg.id,
                                                                          op |-> msg.op,
                                                                      status |-> "FINALIZED"]}]
                   /\  ExecInconsistent(msg.op)
       \/  /\ msg.op.type = "Consensus"
           /\  \/  /\  \E  rec \in rRecord [S][r] :
                       /\  rec.msgid = msg.id
                       /\  rec.op = msg.op (*Replica knows of this op*)
                       /\  \/  /\  rec.status = "TENTATIVE" (*Operation tentative*)
                               /\  rRecord' = [rRecord EXCEPT ! [S][r] = (@ \ {rec}) \cup {[msgid |-> msg.id,
                                                                                               op |-> msg.op,
                                                                                              res |-> msg.res,
                                                                                           status |-> "FINALIZED"]}]
                               /\  Send([type |-> "CONFIRM",
                                         v |-> rViewNumber [S][r],
                                         id |-> msg.id,
                                         op |-> msg.op,
                                        res |-> msg.res,
                                        src |-> r])
                                  /\  IF rec.res /=  msg.res THEN UpdateConsensus(msg.op, msg.res) ELSE true
                           \/  /\  rec.status = "FINALIZED" (*Operation already finalized (view change happened in the meantime)*)
                               /\  Send([type |-> "CONFIRM",
                                   v |-> rViewNumber [S][r],
                                   id |-> msg.id,
                                   op |-> msg.op,
                                   res |-> rec.res,
                                   src |-> r])
                               /\  UNCHANGED <<rRecord>>
               \/  /\  ~\E  rec \in rRecord [S][r] : (* Replica didn't hear of this op *)
                        /\  rec.msgid = msg.id
                        /\  rec.op = msg.op
                   /\  rRecord' = [rRecord EXCEPT ! [S][r] = @ \cup {[msgid |-> msg.id,
                                                                         op |-> msg.op,
                                                                        res |-> msg.res,
                                                                     status |-> "FINALIZED"]}]
                   /\  Send([type |-> "CONFIRM",
                                v |-> rViewNumber [S][r],
                               id |-> msg.id,
                               op |-> msg.op,
                              res |-> msg.res,
                              src |-> r])
                   /\  ExecuteAndUpdateConsensus(msg.op, msg.res)
   /\  UNCHANGED <<rState, rViewNumber, rViewReplies, cVars, aVars, gViewChangesNo>>


(* A replica starts the view change procedure supports concurrent view changes (id by src) *)
ReplicaStartViewChange(r) ==
 /\  Send([type |-> "START-VIEW-CHANGE",
              v |-> rViewNumber [r],
            src |-> r])
 /\  rState' = [rState EXCEPT ! [r] = "RECOVERING"]
 /\  UNCHANGED <<rViewNumber, rViewReplies, rRecord, cVars, aVars>>
 /\  gViewChangesNo < max_vc (*BOUND on number of view changes*)

 /\  gViewChangesNo' = gViewChangesNo + 1


(* A replica received a message to start view change *)
ReplicaReceiveStartViewChange(r) ==
 /\  \E msg \in sentMsg [S] :
        /\ msg.type = "START-VIEW-CHANGE"
        /\  LET v_new ==
              IF msg.v > rViewNumber [r] THEN msg.v
              ELSE rViewNumber [S][r]
            IN
              /\  ~\E m \in sentMsg [S] : (*not already sent (just to bound the model checker) *)
                  /\ m.type = "DO-VIEW-CHANGE"
                  /\ m.v >= msg.v
                  /\ m.dst = msg.src
                  /\ m.src = r
              /\  Send([type |-> "DO-VIEW-CHANGE",
                           v |-> v_new + 1,
                           r |-> rRecord [r],
                         src |-> r,
                         dst |-> msg.src])
              /\  rViewNumber' = [rViewNumber EXCEPT ! [S][r] = v_new + 1]
 /\  rState' = [rState EXCEPT ! [S][r] = "VIEW-CHANGING"]
 /\  UNCHANGED <<cVars, rRecord, rViewReplies, aVars, gViewChangesNo>>


(* Replica received DO-VIEW-CHANGE message *)
ReplicaReceiveDoViewChange(r) ==
 /\  \E msg \in sentMsg [S] :
        /\ msg.type = "DO-VIEW-CHANGE"
        /\ msg.dst = r
        /\ msg.v > rViewNumber [r]
        /\  rViewReplies' = [rViewReplies EXCEPT ! [r] = @ \cup {[    type |-> "do-view-change",
                                                                viewNumber |-> msg.v,
                                                                         r |-> msg.r,
                                                                       src |-> msg.src]}]
 /\  UNCHANGED <<cVars, rViewNumber, rRecord, rState, aVars, oVars>>


(* A replica received enough view change replies to start processing in the new view *)
ReplicaDecideNewView(r) ==
 /\  \E Q \in Quorums :
        /\  \A  rep \in Q : \E  reply \in rViewReplies[r] :                  /\  reply.src = rep
                                                                             /\  reply.type = "do-view-change"
                                                           
(*received at least a quorum of replies*)
        /\  LET recoveredConensusOps_a ==
(*any consensus operation found in at least a majority of a Quorum*)
            {x \in UNION {y.r : y \in {z \in rViewReplies[S][r] : z.src \in Q}} :

               /\  x [2].type = "Consensus"
               /\  \E P \in SuperQuorums :
                      \A  rep \in Q \cap P :
                        \E  reply \in rViewReplies[r] :
                           /\  reply.src = rep
                           /\  x \in reply.r} (* same op, same result *)

                recoveredConensusOps_b == (* TODO : what result? from the app? the rest of consensus ops found in at least one record (discard the result) *) {<<z [1], z [2]>> :
                                z \in {x \in UNION {y.r : y \in {z \in rViewReplies[S][r] : z.src \in Q}} :
                                   /\  x[2].type = "Consensus"
                                   /\  ~x \in recoveredConensusOps_a}}

                recoveredInconsistentOps_c ==
(*any inconsistent operation found in any received record (discard the result) *)
                   {<<z [1], z [2]>> :
                      z \in {x \in UNION {y.r : y \in {z \in rViewReplies[S][r] : z.src \in Q}} :
                         x[2].type = "Inconsistent"}}

            IN
              /\ AppRecoverOpsResults(recoveredConensusOps_a)
              /\ AppRecoverOps(recoveredConensusOps_b)
              /\ AppRecoverOps(recoveredInconsistentOps_c)
              /\  rRecord' = [rRecord EXCEPT ! [S][r] = @ \cup  recoveredConensusOps_a
                                                          \cup  recoveredConensusOps_b
                                                          \cup  recoveredInconsistentOps_c]

        /\  LET v_new ==
(*max view number received*)
               CHOOSE v \in {x.viewNumber : x \in rViewReplies[r]} :
                   \A  y \in rViewReplies[r] :
                       y.viewNumber \leq  v
            IN
               /\  Send([type |-> "START-VIEW",
                            v |-> v_new,
                          src |-> r])
               /\  rViewNumber' = [rViewNumber EXCEPT ! [r] = v_new]

 /\  rViewReplies' = [rViewReplies EXCEPT ! [r] = {}]
 /\  UNCHANGED <<rState, cVars, aVars, gViewChangesNo>>


(*A replica receives a start view message*)
ReplicaReceiveStartView(r) ==
 /\  \E msg \in sentMsg :
     /\ msg.type = "START-VIEW"
     /\ msg.v >= rViewNumber [r]
     /\ msg.src /=  r (* don't reply to myself *)
     /\  Send([type |-> "START-VIEW-REPLY",
                  v |-> msg.v,
                  src |-> r,
                  dst |-> msg.src])
     /\  rViewNumber' = [rViewNumber EXCEPT ! [r] = msg.v]
 /\  rState' = [rState EXCEPT ! [r] = "NORMAL"]
 /\  UNCHANGED <<rRecord, rViewReplies, cVars, aVars, gViewChangesNo>>

ReplicaReceiveStartViewReply(r) ==
 /\  \E msg \in sentMsg :
     /\ msg.type = "START-VIEW-REPLY"
     /\ msg.dst = r
     /\ msg.v > rViewNumber [r] (* receive only if bigger than the last view I was in *)
     /\  rViewReplies' = [rViewReplies EXCEPT ! [S][r] = @ \cup 
                                                            {[      type |-> "start-view-reply",
                                                              viewNumber |-> msg.v,
                                                                       r |-> {},
                                                                     src |-> msg.src]}]
 /\ UNCHANGED <<rRecord, rState, rViewNumber, cVars, aVars, oVars>>

ReplicaRecover(r) == (* we received enough START-VIEW-REPLY messages  *)
 \E Q \in Quorums :
    /\  r \in Q
    /\  \A  p \in Q : \/  p = r
                      \/  /\  p /= r
                          /\  \E  reply \in rViewReplies[S][r] : /\  reply.src = p
                                                                 /\  reply.type = "start-view-reply"
 /\ rViewReplies' = [rViewReplies EXCEPT ! [S][r] = {}]
 /\ rState' = [rState EXCEPT ! [r] = "NORMAL"]
 /\ UNCHANGED <<rRecord, rViewNumber, cVars, aVars, oVars>>


ReplicaResumeViewChange(r) == false (*TODO : On timeout *)


(* A replica fails and looses everything *)
ReplicaFail(r) == (* TODO : check cardinality *)
 /\  rState' = [rState EXCEPT ! [S][r] = "FAILED"]
 /\  rRecord' = [rRecord EXCEPT ! [S][r] = {}]
 /\  rViewNumber' = [rViewNumber EXCEPT ! [r] = 0] \* TODO : check what happens if we loose the view number
 /\  rViewReplies' = [rViewReplies EXCEPT ! [S][r] = {}]
 /\  UNCHANGED <<rViewNumber, cVars, aVars, oVars>>
 /\  Cardinality({re \in Replicas :
(*We assume less than f replicas are allowed to fail*)
                              \/  rState[S][re] = "FAILED"
                              \/  rState[S][re] = "RECOVERING"}) < f

------------------------------------------
(****************************************)
(* High-Level Actions *)
(****************************************)


ClientAction(c) ==
 \/  /\  cState[c] = "NORMAL"
     /\  \/  ClientRequest(c) \* some client tries to replicate commit an operation
         \/  ClientReceiveReply(c) (*some client receives a reply from a replica*)
         \/  ClientReceiveConfirm(c) (*some client receives a confirm from a replica*)
         \/  ClientFail(c) \* some client fails
         \/  ClientDecideOp(c) (*an operation is successful at some client*)
         \/  ClientFinalizedOp(c) \* an operation was finalized at some client
 \/  /\  cState[c] = "FAILED"
     /\  \/  ClientRecover(c)

ReplicaAction(r) ==
 \/  /\  rState[S][r] = "NORMAL"
     /\  \/  ReplicaReceiveRequest(r) (*some replica sends a reply to a REQUEST msg*)
         \/  ReplicaReceiveFinalize(r)
         \/  ReplicaReceiveStartViewChange(r)
         \/  ReplicaReceiveStartView(r)
         \/  ReplicaFail(r) \* some replica fails
 \/  /\  rState[S][r] = "FAILED"
     /\  \/  ReplicaStartViewChange(r) \* some replica starts to recover
 \/  /\  rState[r] = "RECOVERING" \* just to make it clear
     /\  \/  ReplicaReceiveDoViewChange(r)
         \/  ReplicaDecideNewView(r)
         \/  ReplicaReceiveStartViewReply(r)
         \/  ReplicaRecover(r)
 \/  /\  rState[S][r] = "VIEW-CHANGING"
     /\  \/  ReplicaReceiveStartViewChange(r)
         \/  ReplicaReceiveStartView(r)
         \/  ReplicaResumeViewChange(r) \* some timeout expired and view change not finished
         \/  ReplicaFail(r)

Next ==
 \/  \E  c \in Clients : ClientAction(c)
 \/  \E  r \in Replicas : ReplicaAction(r)

Spec == Init /\ [][Next]_vars

FaultTolerance ==
 /\  \A  successfulOp \in aSuccessful, Q \in Quorums :
  (\A  r \in Q : rState[S][r] = "NORMAL" \/  rState[S][r] = "VIEW-CHANGING")
        => (\E  p \in Q : \E  rec \in rRecord [S][p] :
          /\  successfulOp.msgid = rec.msgid
          /\  successfulOp.op = rec.op) (*Not necessarily same result*)
 /\  \A finalizedOp \in aSuccessful, Q \in Quorums :
        (\A  r \in Q : rState[r] = "NORMAL" \/  rState[r] = "VIEW-CHANGING")
     => (\E P \in SuperQuorums :
           \A  p \in Q \cap P :
              \E  rec \in rRecord [p] :
                  finalizedOp = rec)

Inv == TypeOK /\  FaultTolerance

========================================

