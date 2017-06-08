--------------------------- MODULE TAPIR ----------------
(*
This is a TLA+ specification of the TAPIR algorithm.
*)
EXTENDS FiniteSets, Naturals, TLC, TLAPS

Max (S) == if S = {} then 0 else CHOOSE i \in S : \A  j \in S : j \leq  i

(*
TAPIR constants:
1. Shards: function from shard id to set of replica ids in the shard
2. Transactions: set of all possible transactions
3. nr shards: number of shards
*)

CONSTANTS Shards, Transactions, NrShards
(* Note: assume unique number ids for replicas *)


(* IR constants & variables (description in the IR module) *)
CONSTANTS Clients, Quorums, SuperQuorums,
          max\_vc, max req, f
          
VARIABLES rState, rRecord, rViewNumber, rViewReplies, sentMsg, cCrtOp,
cCrtOpToFinalize, cMsgCounter, cCrtOpReplies, cCrtOpConfirms,
cState, aSuccessful, gViewChangesNo

irReplicaVars == <<rState, rRecord, rViewNumber, rViewReplies>>

irClientVars == <<cCrtOp, (*current operation at a client*)
cCrtOpReplies, (*current operation replies*)
cMsgCounter,
cState,
cCrtOpToFinalize,
cCrtOpConfirms>> (*Client variables.*)

irAppVars == <<aSuccessful>> (*Application variables*)

irOtherVars == <<sentMsg, gViewChangesNo>> (*Other variables.*)

(*
TAPIR Variables/State: 1. State at each replica:
rPrepareTxns = List of txns this replica is prepared to commit
rTxnsLog = Log of committed and aborted txns in ts order
rStore = Versioned store
rBkpTable = Table of txns for which this replica
        is the bkp coordinator
2. State of communication medium: sentMsg = sent (and duplicate) messages
3. State at client: cCrtTxn = crt txn requested by the client
*)

(*TAPIR variables & data structures*)
VARIABLES rPreparedTxns, rStore, rTxnsLogAborted, rTxnsLogCommited, rClock, cCrtTxn, cClock

tapirReplicaVars == <<rPreparedTxns, rStore, rTxnsLogAborted, rTxnsLogCommited, rClock>>

tapirClientVars == <<cCrtTxn, cClock>>


StoreEntry == [vs : Nat, val : Nat] (*vs = version*)

Store == [    key : Nat,
          entries : SUBSET StoreEntry,
         latestVs : Nat,
        latestVal : Nat]

TransactionTs == [cid : Clients, clock : Nat] (*Timestamp*)

ReadSet == [key : Nat, val : Nat, vs : Nat]

WriteSet == [key : Nat, val : Nat]

Transaction == [  rSet : subset ReadSet,
                  wSet : subset WriteSet,
                shards : subset Nat]

TypeOK ==
 /\  rStore \in [UNION {Shards[i] : i \in 1 .. NrShards} -> SUBSET Store]
 /\  rPreparedTxns \in [UNION {Shards[i] : i \in 1 .. NrShards} -> SUBSET Transaction]
 /\  rTxnsLogAborted \in [UNION {Shards[i] : i \in 1 .. NrShards} -> SUBSET Transaction]
 /\  rTxnsLogCommited \in [UNION {Shards[i] : i \in 1 .. NrShards} -> SUBSET Transaction]

TAPIRResults == {"Prepare-OK", "Retry", "Prepare-Abstain", "Abort"}

TAPIROpType == {"Prepare", "ABORT", "COMMIT"}

TAPIROpBody == [opType : TAPIROpType, txn : Transaction]

TAPIRClientFail == true (*state we lose at the app level*)

TAPIRReplicaFail == true (*state we lose at the app level*)


(*TAPIR implementation of IR interface*)
TAPIRExecInconsistent(op) == true

TAPIRExecConsensus(op) == IF op.type = "Consensus" THEN "Prepare-OK" ELSE "Abort"

TAPIRDecide(results) == true

TAPIRMerge(d, u) == true

TAPIRSync(records) == true

TAPIRSuccessfulInconsistentOp(op) == true

TAPIRSuccessfulConsensusOp(op, res) == true


(*Initialize for all shards *)
InitIR ==
 /\  rState = [s \in 1 .. NrShards |-> [r \in Shards[s] |-> "NORMAL"]]
 /\  rRecord = [s \in 1 .. NrShards |-> [r \in Shards[s] |-> {}]]
 /\  rViewNumber = [s \in 1 .. NrShards |-> [r \in Shards[s] |-> 0]]
 /\  rViewReplies = [s \in 1 .. NrShards |-> [r \in Shards[s] |-> {}]]
 /\  sentMsg = [s \in 1 .. NrShards |-> {}]
 /\  cCrtOp = [s \in 1 .. NrShards |-> [c \in Clients |-> <<>>]]
 /\  cCrtOpToFinalize = [s \in 1 .. NrShards |-> [c \in Clients |-> <<>>]]
 /\  cMsgCounter = [s \in 1 .. NrShards |-> [c \in Clients |-> 0]]
 /\  cCrtOpReplies = [s \in 1 .. NrShards |-> [c \in Clients |-> {}]]
 /\  cCrtOpConfirms = [s \in 1 .. NrShards |-> [c \in Clients |-> {}]]
 /\  cState = [c \in Clients |-> "NORMAL"]
 /\  aSuccessful = {}
 /\  gViewChangesNo = [s \in 1 .. NrShards |-> 0]


(* IR instance per shard TODO : modify replica also *)
IR(s) == INSTANCE IR\_consensus WITH AppClientFail <-  TAPIRClientFail,
                                     AppReplicaFail <-  TAPIRReplicaFail,
                                     OpBody <-  TAPIROpBody,
                                     ExecInconsistent <-  TAPIRExecInconsistent,
                                     ExecConsensus <-  TAPIRExecConsensus,
                                     Merge <-  TAPIRMerge,
                                     Sync <-  TAPIRSync,
                                     SuccessfulInconsistentOp <-  TAPIRSuccessfulInconsistentOp,
                                     SuccessfulConsensusOp <-  TAPIRSuccessfulConsensusOp,
                                     Decide <-  TAPIRDecide,
                                     Results <-  TAPIRResults,
                                     Replicas <-  Shards[s],
                                     Quorums <-  Quorums[s],
                                     SuperQuorums <-  SuperQuorums[s],
                                     S <-  s


(*TAPIR messages*)
Message ==
        [type : {"READ"},
          key : Nat,
          dst : UNION Shards]
 \cup 
        [type : {"READ-REPLY"},
          key : Nat,
          val : Nat,
           vs : Nat, (*version*)
          dst : Clients]
 \cup 
        [type : {"READ-VERSION"},
          key : Nat,
           vs : Nat,
          dst : UNION Shards]
 \cup 
        [type : {"READ-VERSION-REPLY"},
          key : Nat,
           vs : Nat,
          dst : Clients]

InitTAPIR == /\  cCrtTxn = [c \in Clients |-> <<>>]
 /\  cClock = [c \in Clients |-> 0]
 /\  rPreparedTxns = [s \in 1 .. NrShards |-> [r \in Shards[s] |-> {}]]
 /\  rStore = [r \in UNION {Shards[i] : i \in 1 .. NrShards} |-> {}]
 /\  rTxnsLogAborted = [s \in 1 .. NrShards |-> [r \in Shards[s] |-> {}]]
 /\  rClock = [s \in 1 .. NrShards |-> [r \in Shards[s] |-> 0]]


Init == InitIR /\  InitTAPIR

---------------------------------------------
(****************************************)
(* Tapir replica actions *)
(****************************************)

TAPIRReplicaReceiveRead(r) == true

TAPIRReplicaAction(r) ==
 \/  /\  rState[r] = "NORMAL"
     /\  \/  TAPIRReplicaReceiveRead(r)


---------------------------------------------
(****************************************)
(* Tapir client actions *)
(****************************************)

TAPIRClientExecuteTxn(c) ==
(*
first, resolve all reads (read from any replica and get the vs)
then send prepares in all shard involved by seting the cCrtOp in the
respective IR shard instance
TODO : for now just simulate this, pick a transaction from
transaction pool, get some versions from the replica
stores
*)

 /\  cCrtTxn[c] = <<>>
 /\  \E  t \in Transactions :
     LET rSet == {rse \in ReadSet :
                      /\  \E  trse \in t.rSet : rse = trse
                      /\  LET
                             r == Max ({r \in Shards[(rse.key%NrShards) + 1] :
                             \E  se \in rStore[r] : rse.key = se.key})
                          IN
                             /\  r /= 0
                             /\  \E  se \in rStore[r] :
                             /\  rse.key = se.key
                             /\  rse.val = se.latestVal
                             /\  rse.vs = se.latestVs
                 }

shards == {s \in 1 .. NrShards :
             \/  \E  trse \in t.rSet : s = (trse.key%NrShards) + 1
             \/  \E  twse \in t.wSet : s = (twse.key%NrShards) + 1}
     IN
        /\  Cardinality(rSet) = Cardinality(t.rSet) (*found all the reads*)
        /\  cCrtTxn' = [cCrtTxn except ! [c] = [rSet |-> rSet,
                                                wSet |-> t.wSet,
                                              shards |-> shards]]
 /\  UNCHANGED <<irReplicaVars, irClientVars, irOtherVars, irAppVars, tapirReplicaVars, cClock>>

TAPIRClientPrepareTxn(c) ==
 /\  cCrtTxn[c] /=  <<>>
 /\  \E  s \in cCrtTxn[c].shards : (* prepare in shard s *)
                             (* - ok if already prepared *)
      /\  IR(s) !ClientRequest(c, [type |-> "Consensus",
                                   body |-> <<"Prepare", cCrtTxn>>])
 /\  UNCHANGED <<irReplicaVars, irAppVars,
                 cCrtOpReplies,
                 cCrtOpConfirms,
                 cCrtOpToFinalize,
                 gViewChangesNo,
                 cState, tapirClientVars, tapirReplicaVars>>

TAPIRClientAction(c) ==
 \/  /\  cState[c] = "NORMAL"
     /\  \/  TAPIRClientExecuteTxn(c) (* for now just simulate this
(don't send explicit READ messages) *)
 \/  TAPIRClientPrepareTxn(c)
 \/  2PC(c)

-------------------------------------------------
(****************************************)
(* High-Level Actions *)
(****************************************)

Next ==
  /\  \/  \E  c \in Clients : TAPIRClientAction(c)
      \/  /\  \E  s \in 1 .. NrShards : IR(s) !Next
          /\  UNCHANGED <<tapirClientVars, tapirReplicaVars>>

Inv == Cardinality(aSuccessful) < 2


========================================
