/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-08 21:12:22
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot
open util/buffer[bufIdx0, Transaction] as currentTxn
open util/buffer[bufIdx1, Transaction] as pendingTxn

abstract sig Response {}
one sig Commit, Abort extends Response{}

sig Key, Value {}
sig Transaction {
	 // The Coordinator managing this transaction
	coordinator: lone CoordinatorID,
	 // Updated keys and values
	key: Key -> Value
}

fact {
	all t: Transaction | one t.key // Limit each transaction to updating one key only
}

abstract sig DshStates {}
abstract sig Carousel extends DshStates {} 
abstract sig Carousel_Client extends Carousel {} 
one sig Carousel_Client_Reading extends Carousel_Client {} 
one sig Carousel_Client_Waiting extends Carousel_Client {} 
abstract sig Carousel_Coordinator extends Carousel {} 
one sig Carousel_Coordinator_Replicate extends Carousel_Coordinator {} 
one sig Carousel_Coordinator_WaitForResponse extends Carousel_Coordinator {} 
abstract sig Carousel_PartitionLeader extends Carousel {} 
one sig Carousel_PartitionLeader_Waiting extends Carousel_PartitionLeader {} 
one sig Carousel_PartitionLeader_Commit extends Carousel_PartitionLeader {} 
one sig Carousel_PartitionLeader_Abort extends Carousel_PartitionLeader {} 

abstract sig DshIds {}
sig ClientID extends DshIds {} 
sig PartLdrID extends DshIds {} 
sig CoordinatorID extends DshIds {} 

sig bufIdx0 {}
sig bufIdx1 {}
sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_sc_used1: DshIds -> DshStates,
  dsh_conf1: DshIds -> DshStates,
  dsh_stable: one boolean/Bool,
  Carousel_Client_response: ClientID -> lone Response,
  Carousel_Client_data: ClientID -> (Key ->lone Value),
  Carousel_Client_txn: ClientID -> lone Transaction,
  Carousel_Client_transToSend: ClientID -> set Transaction,
  Carousel_Coordinator_currentTxn: CoordinatorID -> lone
                                   Transaction,
  Carousel_Coordinator_client: CoordinatorID -> lone ClientID,
  Carousel_Coordinator_info: CoordinatorID ->
                             (Key ->lone Value),
  Carousel_Coordinator_coord_responses: CoordinatorID ->
                                        (PartLdrID ->lone
                                           Response),
  Carousel_PartitionLeader_response: PartLdrID ->
                                     (Transaction ->lone
                                        Response),
  Carousel_PartitionLeader_data: PartLdrID ->
                                 (Key ->lone Value),
  Carousel_PartitionLeader_currentTxn: PartLdrID ->
                                       (bufIdx0 ->
                                          Transaction),
  Carousel_PartitionLeader_pendingTxn: PartLdrID ->
                                       (bufIdx1 ->
                                          Transaction)
}

pred dsh_initial [
	s: one DshSnapshot] {
  (all p0_ClientID: one
  ClientID,p1_CoordinatorID: one
  CoordinatorID,p2_PartLdrID: one
  PartLdrID | (s.dsh_conf0) = none and
                (s.dsh_conf1) =
                  (((ClientID -> Carousel_Client_Reading) +
                      (CoordinatorID ->
                         Carousel_Coordinator_Replicate)) +
                     (PartLdrID ->
                        Carousel_PartitionLeader_Waiting)) and
                (s.dsh_sc_used1) = (none -> none) and
                no
                p1_CoordinatorID.(s.Carousel_Coordinator_client) and
                no
                p1_CoordinatorID.(s.Carousel_Coordinator_coord_responses) and
                no
                p1_CoordinatorID.(s.Carousel_Coordinator_info) and
                no
                p1_CoordinatorID.(s.Carousel_Coordinator_currentTxn) and
                (all disj p,q: PartLdrID | (p.(s.Carousel_PartitionLeader_data)) =
                                             (q.(s.Carousel_PartitionLeader_data))) and
                (all disj p,q: PartLdrID | (p.(s.Carousel_PartitionLeader_pendingTxn)) =
                                             (q.(s.Carousel_PartitionLeader_pendingTxn))) and
                no
                p2_PartLdrID.(s.Carousel_PartitionLeader_response) and
                one
                p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn) and
                no
                p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn) and
                no
                p0_ClientID.(s.Carousel_Client_response) and
                some
                p0_ClientID.(s.Carousel_Client_data) and
                no
                p0_ClientID.(s.Carousel_Client_txn) and
                (#
                  p0_ClientID.(s.Carousel_Client_transToSend)) =
                  (2))
  (s.dsh_stable).boolean/isTrue
}

pred Carousel_Client_Waiting_FinalizeCommit_pre [
	s: one DshSnapshot,
	p0_ClientID: one ClientID] {
  some
((p0_ClientID -> Carousel_Client_Waiting) & (s.dsh_conf1))
  one
  p0_ClientID.(s.Carousel_Client_response) and
  Commit in p0_ClientID.(s.Carousel_Client_response)
  !(Carousel in (s.dsh_sc_used0))
  !((p0_ClientID -> Carousel_Client) in (s.dsh_sc_used1))
}


pred Carousel_Client_Waiting_FinalizeCommit_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) -
       (p0_ClientID -> Carousel_Client_Reading)) -
      (p0_ClientID -> Carousel_Client_Waiting)) +
     (p0_ClientID -> Carousel_Client_Reading))
  (p0_ClientID.(sn.Carousel_Client_data)) =
  ((p0_ClientID.(s.Carousel_Client_txn)).key) and
  (p0_ClientID.(sn.Carousel_Client_txn)) = none and
  no
  p0_ClientID.(sn.Carousel_Client_response)
  ((p0_ClientID -> Carousel_Client).(none.(none.(none.(p0_ClientID.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_ClientID -> Carousel_Client)))
       )

}

pred Carousel_Client_Waiting_FinalizeCommit_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_ClientID -> Carousel_Client_Waiting) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(Carousel in dsh_scp0) and
    !((p0_ClientID -> Carousel_Client) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Carousel_Client_Waiting_FinalizeCommit [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID] {
  p0_ClientID.(s.Carousel_Client_Waiting_FinalizeCommit_pre)
  p0_ClientID.(sn.(s.Carousel_Client_Waiting_FinalizeCommit_post))
}

pred Carousel_PartitionLeader_Abort_AbortTransaction_pre [
	s: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Abort) &
   (s.dsh_conf1))
  !(Carousel in (s.dsh_sc_used0))
  !((p2_PartLdrID -> Carousel_PartitionLeader) in
    (s.dsh_sc_used1))
}


pred Carousel_PartitionLeader_Abort_AbortTransaction_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((((s.dsh_conf1) -
        (p2_PartLdrID -> Carousel_PartitionLeader_Waiting)) -
       (p2_PartLdrID -> Carousel_PartitionLeader_Commit)) -
      (p2_PartLdrID -> Carousel_PartitionLeader_Abort)) +
     (p2_PartLdrID -> Carousel_PartitionLeader_Waiting))
  (p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).removeFirst) and
  ((((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).firstElem).coordinator).(sn.Carousel_Coordinator_coord_responses)) =
    (((((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).firstElem).coordinator).(s.Carousel_Coordinator_coord_responses)) +
       (p2_PartLdrID -> Abort)) and
  no
  p2_PartLdrID.(sn.Carousel_PartitionLeader_response) and
  (all others: CoordinatorID -
                 (((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).firstElem).coordinator) | (others.(sn.Carousel_Coordinator_coord_responses)) =
                                                                                                      (others.(s.Carousel_Coordinator_coord_responses)))
  ((p2_PartLdrID -> Carousel_PartitionLeader).(none.(p2_PartLdrID.(none.(none.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p2_PartLdrID -> Carousel_PartitionLeader)))
       )

}

pred Carousel_PartitionLeader_Abort_AbortTransaction_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Abort) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(Carousel in dsh_scp0) and
    !((p2_PartLdrID -> Carousel_PartitionLeader) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Carousel_PartitionLeader_Abort_AbortTransaction [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  p2_PartLdrID.(s.Carousel_PartitionLeader_Abort_AbortTransaction_pre)
  p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Abort_AbortTransaction_post))
}

pred Carousel_Client_Reading_ReadAndPrepare_pre [
	s: one DshSnapshot,
	p0_ClientID: one ClientID] {
  some
((p0_ClientID -> Carousel_Client_Reading) & (s.dsh_conf1))
  (some c: CoordinatorID | no
  c.(s.Carousel_Coordinator_currentTxn))
  !(Carousel in (s.dsh_sc_used0))
  !((p0_ClientID -> Carousel_Client) in (s.dsh_sc_used1))
}


pred Carousel_Client_Reading_ReadAndPrepare_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) -
       (p0_ClientID -> Carousel_Client_Reading)) -
      (p0_ClientID -> Carousel_Client_Waiting)) +
     (p0_ClientID -> Carousel_Client_Waiting))
  (one t: p0_ClientID.(s.Carousel_Client_transToSend),c: CoordinatorID | (all leader: PartLdrID | (p0_ClientID.(sn.Carousel_Client_txn)) =
                                                                                                  t and
                                                                                                  (c.(sn.Carousel_Coordinator_client)) =
                                                                                                    p0_ClientID and
                                                                                                  no
                                                                                                  c.(s.Carousel_Coordinator_currentTxn) and
                                                                                                  (c.(sn.Carousel_Coordinator_currentTxn)) =
                                                                                                    t and
                                                                                                  (t.coordinator) =
                                                                                                    c and
                                                                                                  t.((leader.(sn.Carousel_PartitionLeader_currentTxn)).((leader.(s.Carousel_PartitionLeader_currentTxn)).add)) and
                                                                                                  (p0_ClientID.(sn.Carousel_Client_transToSend)) =
                                                                                                    ((p0_ClientID.(s.Carousel_Client_transToSend)) -
                                                                                                       t) and
                                                                                                  (all others: CoordinatorID -
                                                                                                                 c | (others.(sn.Carousel_Coordinator_client)) =
                                                                                                                       (others.(s.Carousel_Coordinator_client))) and
                                                                                                  (all others: CoordinatorID -
                                                                                                                 c | (others.(sn.Carousel_Coordinator_currentTxn)) =
                                                                                                                       (others.(s.Carousel_Coordinator_currentTxn)))))
  ((p0_ClientID -> Carousel_Client).(none.(none.(none.(p0_ClientID.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_ClientID -> Carousel_Client)))
       )

}

pred Carousel_Client_Reading_ReadAndPrepare_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_ClientID -> Carousel_Client_Reading) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(Carousel in dsh_scp0) and
    !((p0_ClientID -> Carousel_Client) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Carousel_Client_Reading_ReadAndPrepare [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID] {
  p0_ClientID.(s.Carousel_Client_Reading_ReadAndPrepare_pre)
  p0_ClientID.(sn.(s.Carousel_Client_Reading_ReadAndPrepare_post))
}

pred Carousel_Coordinator_WaitForResponse_StartAbort_pre [
	s: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID] {
  some
((p1_CoordinatorID -> Carousel_Coordinator_WaitForResponse) &
   (s.dsh_conf1))
  some
  p1_CoordinatorID.(s.Carousel_Coordinator_coord_responses) and
  Abort in
    (PartLdrID.(p1_CoordinatorID.(s.Carousel_Coordinator_coord_responses)))
  !(Carousel in (s.dsh_sc_used0))
  !((p1_CoordinatorID -> Carousel_Coordinator) in
    (s.dsh_sc_used1))
}


pred Carousel_Coordinator_WaitForResponse_StartAbort_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (p1_CoordinatorID ->
         Carousel_Coordinator_WaitForResponse)) +
     (p1_CoordinatorID ->
        Carousel_Coordinator_WaitForResponse))
  ((p1_CoordinatorID.(s.Carousel_Coordinator_client)).(sn.Carousel_Client_response)) =
  Abort and
  (all others: ClientID -
                 (p1_CoordinatorID.(s.Carousel_Coordinator_client)) | (others.(sn.Carousel_Client_response)) =
                                                                        (others.(s.Carousel_Client_response))) and
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_info) and
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_currentTxn) and
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_client) and
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_coord_responses)
  ((p1_CoordinatorID -> Carousel_Coordinator).(none.(none.(p1_CoordinatorID.(none.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p1_CoordinatorID -> Carousel_Coordinator)))
       )

}

pred Carousel_Coordinator_WaitForResponse_StartAbort_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p1_CoordinatorID -> Carousel_Coordinator_WaitForResponse) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(Carousel in dsh_scp0) and
    !((p1_CoordinatorID -> Carousel_Coordinator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Carousel_Coordinator_WaitForResponse_StartAbort [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID] {
  p1_CoordinatorID.(s.Carousel_Coordinator_WaitForResponse_StartAbort_pre)
  p1_CoordinatorID.(sn.(s.Carousel_Coordinator_WaitForResponse_StartAbort_post))
}

pred Carousel_PartitionLeader_Waiting_PrepareCommit_pre [
	s: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) &
   (s.dsh_conf1))
  some
  ((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).elems) and
  no
  p2_PartLdrID.(s.Carousel_PartitionLeader_response) and
  !(((((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).firstElem).key).Value) in
      ((((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).elems).key).Value))
  !(Carousel in (s.dsh_sc_used0))
  !((p2_PartLdrID -> Carousel_PartitionLeader) in
    (s.dsh_sc_used1))
}


pred Carousel_PartitionLeader_Waiting_PrepareCommit_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((((s.dsh_conf1) -
        (p2_PartLdrID -> Carousel_PartitionLeader_Waiting)) -
       (p2_PartLdrID -> Carousel_PartitionLeader_Commit)) -
      (p2_PartLdrID -> Carousel_PartitionLeader_Abort)) +
     (p2_PartLdrID -> Carousel_PartitionLeader_Commit))
  ((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).firstElem).((p2_PartLdrID.(sn.Carousel_PartitionLeader_pendingTxn)).((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).add)) and
  (p2_PartLdrID.(sn.Carousel_PartitionLeader_currentTxn)).((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).removeFirst)
  ((p2_PartLdrID -> Carousel_PartitionLeader).(none.(p2_PartLdrID.(none.(none.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p2_PartLdrID -> Carousel_PartitionLeader)))
       )

}

pred Carousel_PartitionLeader_Waiting_PrepareCommit_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(Carousel in dsh_scp0) and
    !((p2_PartLdrID -> Carousel_PartitionLeader) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Carousel_PartitionLeader_Waiting_PrepareCommit [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  p2_PartLdrID.(s.Carousel_PartitionLeader_Waiting_PrepareCommit_pre)
  p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_PrepareCommit_post))
}

pred Carousel_Coordinator_WaitForResponse_StartCommit_pre [
	s: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID] {
  some
((p1_CoordinatorID -> Carousel_Coordinator_WaitForResponse) &
   (s.dsh_conf1))
  (#
  p1_CoordinatorID.(s.Carousel_Coordinator_coord_responses)) =
  (# PartLdrID) and
  !(Abort in
      (PartLdrID.(p1_CoordinatorID.(s.Carousel_Coordinator_coord_responses))))
  !(Carousel in (s.dsh_sc_used0))
  !((p1_CoordinatorID -> Carousel_Coordinator) in
    (s.dsh_sc_used1))
}


pred Carousel_Coordinator_WaitForResponse_StartCommit_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (p1_CoordinatorID ->
         Carousel_Coordinator_WaitForResponse)) +
     (p1_CoordinatorID ->
        Carousel_Coordinator_WaitForResponse))
  ((p1_CoordinatorID.(s.Carousel_Coordinator_client)).(sn.Carousel_Client_response)) =
  Commit and
  (all others: ClientID -
                 (p1_CoordinatorID.(s.Carousel_Coordinator_client)) | (others.(sn.Carousel_Client_response)) =
                                                                        (others.(s.Carousel_Client_response))) and
  (all leader: PartLdrID | (leader.(sn.Carousel_PartitionLeader_response)) =
                             (p1_CoordinatorID.(s.Carousel_Coordinator_currentTxn) ->
                                Commit)) and
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_info) and
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_currentTxn) and
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_client) and
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_coord_responses)
  ((p1_CoordinatorID -> Carousel_Coordinator).(none.(none.(p1_CoordinatorID.(none.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p1_CoordinatorID -> Carousel_Coordinator)))
       )

}

pred Carousel_Coordinator_WaitForResponse_StartCommit_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p1_CoordinatorID -> Carousel_Coordinator_WaitForResponse) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(Carousel in dsh_scp0) and
    !((p1_CoordinatorID -> Carousel_Coordinator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Carousel_Coordinator_WaitForResponse_StartCommit [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID] {
  p1_CoordinatorID.(s.Carousel_Coordinator_WaitForResponse_StartCommit_pre)
  p1_CoordinatorID.(sn.(s.Carousel_Coordinator_WaitForResponse_StartCommit_post))
}

pred Carousel_Client_Waiting_FinalizeAbort_pre [
	s: one DshSnapshot,
	p0_ClientID: one ClientID] {
  some
((p0_ClientID -> Carousel_Client_Waiting) & (s.dsh_conf1))
  one
  p0_ClientID.(s.Carousel_Client_response) and
  Abort in p0_ClientID.(s.Carousel_Client_response)
  !(Carousel in (s.dsh_sc_used0))
  !((p0_ClientID -> Carousel_Client) in (s.dsh_sc_used1))
}


pred Carousel_Client_Waiting_FinalizeAbort_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) -
       (p0_ClientID -> Carousel_Client_Reading)) -
      (p0_ClientID -> Carousel_Client_Waiting)) +
     (p0_ClientID -> Carousel_Client_Reading))
  (p0_ClientID.(sn.Carousel_Client_txn)) = none and
  no
  p0_ClientID.(sn.Carousel_Client_response)
  ((p0_ClientID -> Carousel_Client).(none.(none.(none.(p0_ClientID.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_ClientID -> Carousel_Client)))
       )

}

pred Carousel_Client_Waiting_FinalizeAbort_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p0_ClientID -> Carousel_Client_Waiting) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(Carousel in dsh_scp0) and
    !((p0_ClientID -> Carousel_Client) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Carousel_Client_Waiting_FinalizeAbort [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID] {
  p0_ClientID.(s.Carousel_Client_Waiting_FinalizeAbort_pre)
  p0_ClientID.(sn.(s.Carousel_Client_Waiting_FinalizeAbort_post))
}

pred Carousel_PartitionLeader_Waiting_FinalizeCommit_pre [
	s: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) &
   (s.dsh_conf1))
  Commit in
  (Transaction.(p2_PartLdrID.(s.Carousel_PartitionLeader_response)))
  !(Carousel in (s.dsh_sc_used0))
  !((p2_PartLdrID -> Carousel_PartitionLeader) in
    (s.dsh_sc_used1))
}


pred Carousel_PartitionLeader_Waiting_FinalizeCommit_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (p2_PartLdrID -> Carousel_PartitionLeader_Waiting)) +
     (p2_PartLdrID -> Carousel_PartitionLeader_Waiting))
  no
  p2_PartLdrID.(sn.Carousel_PartitionLeader_response) and
  (p2_PartLdrID.(sn.Carousel_PartitionLeader_pendingTxn)).((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).removeFirst) and
  (p2_PartLdrID.(sn.Carousel_PartitionLeader_data)) =
    (p2_PartLdrID.(s.Carousel_PartitionLeader_data) ++
       (((p2_PartLdrID.(s.Carousel_PartitionLeader_response)).Response).key))
  ((p2_PartLdrID -> Carousel_PartitionLeader).(none.(p2_PartLdrID.(none.(none.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p2_PartLdrID -> Carousel_PartitionLeader)))
       )

}

pred Carousel_PartitionLeader_Waiting_FinalizeCommit_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(Carousel in dsh_scp0) and
    !((p2_PartLdrID -> Carousel_PartitionLeader) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Carousel_PartitionLeader_Waiting_FinalizeCommit [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  p2_PartLdrID.(s.Carousel_PartitionLeader_Waiting_FinalizeCommit_pre)
  p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_FinalizeCommit_post))
}

pred Carousel_PartitionLeader_Waiting_PrepareAbort_pre [
	s: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) &
   (s.dsh_conf1))
  some
  ((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).elems) and
  ((((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).firstElem).key).Value) in
    ((((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).elems).key).Value)
  !(Carousel in (s.dsh_sc_used0))
  !((p2_PartLdrID -> Carousel_PartitionLeader) in
    (s.dsh_sc_used1))
}


pred Carousel_PartitionLeader_Waiting_PrepareAbort_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((((s.dsh_conf1) -
        (p2_PartLdrID -> Carousel_PartitionLeader_Waiting)) -
       (p2_PartLdrID -> Carousel_PartitionLeader_Commit)) -
      (p2_PartLdrID -> Carousel_PartitionLeader_Abort)) +
     (p2_PartLdrID -> Carousel_PartitionLeader_Abort))
  ((p2_PartLdrID -> Carousel_PartitionLeader).(none.(p2_PartLdrID.(none.(none.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p2_PartLdrID -> Carousel_PartitionLeader)))
       )

}

pred Carousel_PartitionLeader_Waiting_PrepareAbort_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(Carousel in dsh_scp0) and
    !((p2_PartLdrID -> Carousel_PartitionLeader) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Carousel_PartitionLeader_Waiting_PrepareAbort [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  p2_PartLdrID.(s.Carousel_PartitionLeader_Waiting_PrepareAbort_pre)
  p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_PrepareAbort_post))
}

pred Carousel_Coordinator_Replicate_Replicating_pre [
	s: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID] {
  some
((p1_CoordinatorID -> Carousel_Coordinator_Replicate) &
   (s.dsh_conf1))
  one p1_CoordinatorID.(s.Carousel_Coordinator_currentTxn)
  !(Carousel in (s.dsh_sc_used0))
  !((p1_CoordinatorID -> Carousel_Coordinator) in
    (s.dsh_sc_used1))
}


pred Carousel_Coordinator_Replicate_Replicating_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) -
       (p1_CoordinatorID -> Carousel_Coordinator_Replicate)) -
      (p1_CoordinatorID ->
         Carousel_Coordinator_WaitForResponse)) +
     (p1_CoordinatorID ->
        Carousel_Coordinator_WaitForResponse))
  (p1_CoordinatorID.(sn.Carousel_Coordinator_info)) =
  ((p1_CoordinatorID.(s.Carousel_Coordinator_currentTxn)).key)
  ((p1_CoordinatorID -> Carousel_Coordinator).(none.(none.(p1_CoordinatorID.(none.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p1_CoordinatorID -> Carousel_Coordinator)))
       )

}

pred Carousel_Coordinator_Replicate_Replicating_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p1_CoordinatorID -> Carousel_Coordinator_Replicate) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(Carousel in dsh_scp0) and
    !((p1_CoordinatorID -> Carousel_Coordinator) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Carousel_Coordinator_Replicate_Replicating [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID] {
  p1_CoordinatorID.(s.Carousel_Coordinator_Replicate_Replicating_pre)
  p1_CoordinatorID.(sn.(s.Carousel_Coordinator_Replicate_Replicating_post))
}

pred Carousel_PartitionLeader_Commit_CommitTransaction_pre [
	s: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Commit) &
   (s.dsh_conf1))
  !(Carousel in (s.dsh_sc_used0))
  !((p2_PartLdrID -> Carousel_PartitionLeader) in
    (s.dsh_sc_used1))
}


pred Carousel_PartitionLeader_Commit_CommitTransaction_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((((s.dsh_conf1) -
        (p2_PartLdrID -> Carousel_PartitionLeader_Waiting)) -
       (p2_PartLdrID -> Carousel_PartitionLeader_Commit)) -
      (p2_PartLdrID -> Carousel_PartitionLeader_Abort)) +
     (p2_PartLdrID -> Carousel_PartitionLeader_Waiting))
  ((((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).firstElem).coordinator).(sn.Carousel_Coordinator_coord_responses)) =
  (((((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).firstElem).coordinator).(s.Carousel_Coordinator_coord_responses)) +
     (p2_PartLdrID -> Commit)) and
  (all others: CoordinatorID -
                 (((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).firstElem).coordinator) | (others.(sn.Carousel_Coordinator_coord_responses)) =
                                                                                                      (others.(s.Carousel_Coordinator_coord_responses)))
  ((p2_PartLdrID -> Carousel_PartitionLeader).(none.(p2_PartLdrID.(none.(none.(sn.(s._testIfNextStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       (sn.dsh_sc_used1) = (none -> none) and
       { (s.dsh_stable).boolean/isTrue or
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse and
       ((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none and
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) and
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p2_PartLdrID -> Carousel_PartitionLeader)))
       )

}

pred Carousel_PartitionLeader_Commit_CommitTransaction_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Commit) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(Carousel in dsh_scp0) and
    !((p2_PartLdrID -> Carousel_PartitionLeader) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred Carousel_PartitionLeader_Commit_CommitTransaction [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  p2_PartLdrID.(s.Carousel_PartitionLeader_Commit_CommitTransaction_pre)
  p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Commit_CommitTransaction_post))
}

pred _testIfNextStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID,
	p1_CoordinatorID: one CoordinatorID,
	p2_PartLdrID: one PartLdrID,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  !(dsh_scp1.(dsh_scp0.(p0_ClientID.(sn.(s.Carousel_Client_Waiting_FinalizeCommit_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Abort_AbortTransaction_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_ClientID.(sn.(s.Carousel_Client_Reading_ReadAndPrepare_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p1_CoordinatorID.(sn.(s.Carousel_Coordinator_WaitForResponse_StartAbort_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_PrepareCommit_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p1_CoordinatorID.(sn.(s.Carousel_Coordinator_WaitForResponse_StartCommit_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_ClientID.(sn.(s.Carousel_Client_Waiting_FinalizeAbort_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_FinalizeCommit_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_PrepareAbort_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p1_CoordinatorID.(sn.(s.Carousel_Coordinator_Replicate_Replicating_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Commit_CommitTransaction_enabledAfterStep)))))
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (some p0_ClientID: one
  ClientID,p1_CoordinatorID: one
  CoordinatorID,p2_PartLdrID: one
  PartLdrID | { p0_ClientID.(sn.(s.Carousel_Client_Waiting_FinalizeCommit)) or
                  p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Abort_AbortTransaction)) or
                  p0_ClientID.(sn.(s.Carousel_Client_Reading_ReadAndPrepare)) or
                  p1_CoordinatorID.(sn.(s.Carousel_Coordinator_WaitForResponse_StartAbort)) or
                  p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_PrepareCommit)) or
                  p1_CoordinatorID.(sn.(s.Carousel_Coordinator_WaitForResponse_StartCommit)) or
                  p0_ClientID.(sn.(s.Carousel_Client_Waiting_FinalizeAbort)) or
                  p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_FinalizeCommit)) or
                  p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_PrepareAbort)) or
                  p1_CoordinatorID.(sn.(s.Carousel_Coordinator_Replicate_Replicating)) or
                  p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Commit_CommitTransaction)) })
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}

