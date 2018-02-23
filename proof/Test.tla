--------------------------------- MODULE Test ---------------------------------
(***************************************************************************)
(* This is a TLA+ specification of the Inconsistent Replication algorithm. *)
(* (And a mechanically-checked proof of its correctness using TLAPS)       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

VARIABLES rViewReplies, recoveredOps

OpType == {"Inconsistent", "Consensus"}
OpStatus == {"TENTATIVE", "FINALIZED"}
Operations == [type: OpType, body: Nat]

TypeOK ==
  /\ rViewReplies \in SUBSET ([lv: Nat,
                               r: SUBSET ([msgid: Nat,
                                           op: Operations,
                                           res: Nat,
                                           status: OpStatus]
                                     \cup [msgid: Nat,
                                           op: Operations,
                                           status: OpStatus]),
                               src: Nat])

A == 
  rViewReplies

B ==
  \* set of all records received in replies in A
  UNION {x.r: x \in A}

test_recoveredConensusOps_R ==
  \* any finalized consensus operation (in at least one record, in the maximum
  \* latest view)
  {x \in B:
     /\ x.op.type = "Consensus"
     /\ x.status = "FINALIZED"
     /\ LET most_updated_reply ==
             CHOOSE reply \in A:
                          /\ \E rec \in reply.r: /\ rec.msgid = x.msgid
                                                 /\ rec.status = "FINALIZED"
                          /\ \A rep \in A:
                            IF \E rec \in rep.r: /\ rec.msgid = x.msgid
                                                 /\ rec.status = "FINALIZED"
                            THEN rep.lv <= reply.lv
                            ELSE TRUE
                   IN
                     x \in most_updated_reply.r}

Init ==
  /\ rViewReplies = {[lv |-> 1, r |-> {[msgid |-> 1, op |-> [type |-> "Consensus", body |-> 1], res |-> 1, status |-> "FINALIZED"]}, src |-> 1],
                     [lv |-> 2, r |-> {[msgid |-> 1, op |-> [type |-> "Consensus", body |-> 1], res |-> 2, status |-> "FINALIZED"]}, src |-> 2],
                     [lv |-> 3, r |-> {[msgid |-> 1, op |-> [type |-> "Consensus", body |-> 1], res |-> 3, status |-> "FINALIZED"]}, src |-> 3]}
  /\ recoveredOps = {}

Next ==
  /\ recoveredOps' = test_recoveredConensusOps_R
  /\ Assert(Cardinality(recoveredOps) = 0, "Should fail")
  /\ UNCHANGED <<rViewReplies>>

=============================================================================
\* Modification History
\* Last modified Fri Apr 24 14:34:42 PDT 2015 by aaasz
\* Created Fri Dec 12 17:42:14 PST 2014 by aaasz
