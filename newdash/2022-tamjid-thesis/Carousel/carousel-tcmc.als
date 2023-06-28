/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-28 18:42:16
*/

open util/boolean
open util/tcmc[DshSnapshot]
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
abstract sig DshScopes {}
one sig CarouselScope extends DshScopes {} 
one sig Carousel_ClientScope extends DshScopes {} 
abstract sig Carousel_Client extends Carousel {} 
one sig Carousel_Client_ReadingScope extends DshScopes {} 
one sig Carousel_Client_Reading extends Carousel_Client {} 
one sig Carousel_Client_WaitingScope extends DshScopes {} 
one sig Carousel_Client_Waiting extends Carousel_Client {} 
one sig Carousel_CoordinatorScope extends DshScopes {} 
abstract sig Carousel_Coordinator extends Carousel {} 
one sig Carousel_Coordinator_ReplicateScope extends DshScopes {} 
one sig Carousel_Coordinator_Replicate extends Carousel_Coordinator {} 
one sig Carousel_Coordinator_WaitForResponseScope extends DshScopes {} 
one sig Carousel_Coordinator_WaitForResponse extends Carousel_Coordinator {} 
one sig Carousel_PartitionLeaderScope extends DshScopes {} 
abstract sig Carousel_PartitionLeader extends Carousel {} 
one sig Carousel_PartitionLeader_WaitingScope extends DshScopes {} 
one sig Carousel_PartitionLeader_Waiting extends Carousel_PartitionLeader {} 
one sig Carousel_PartitionLeader_CommitScope extends DshScopes {} 
one sig Carousel_PartitionLeader_Commit extends Carousel_PartitionLeader {} 
one sig Carousel_PartitionLeader_AbortScope extends DshScopes {} 
one sig Carousel_PartitionLeader_Abort extends Carousel_PartitionLeader {} 

abstract sig Transitions {}
one sig NO_TRANS extends Transitions {} 
one sig Carousel_Client_Waiting_FinalizeCommit extends Transitions {} 
one sig Carousel_PartitionLeader_Abort_AbortTransaction extends Transitions {} 
one sig Carousel_Client_Reading_ReadAndPrepare extends Transitions {} 
one sig Carousel_Coordinator_WaitForResponse_StartAbort extends Transitions {} 
one sig Carousel_PartitionLeader_Waiting_PrepareCommit extends Transitions {} 
one sig Carousel_Coordinator_WaitForResponse_StartCommit extends Transitions {} 
one sig Carousel_Client_Waiting_FinalizeAbort extends Transitions {} 
one sig Carousel_PartitionLeader_Waiting_FinalizeCommit extends Transitions {} 
one sig Carousel_PartitionLeader_Waiting_PrepareAbort extends Transitions {} 
one sig Carousel_Coordinator_Replicate_Replicating extends Transitions {} 
one sig Carousel_PartitionLeader_Commit_CommitTransaction extends Transitions {} 

abstract sig DshIds {}
sig ClientID extends DshIds {} 
sig PartLdrID extends DshIds {} 
sig CoordinatorID extends DshIds {} 

sig bufIdx0 {}
sig bufIdx1 {}
sig DshSnapshot {
  dsh_sc_used0: set DshScopes,
  dsh_conf0: set DshStates,
  dsh_taken0: set Transitions,
  dsh_sc_used1: DshIds -> DshScopes,
  dsh_conf1: DshIds -> DshStates,
  dsh_taken1: DshIds -> Transitions,
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
  PartLdrID | (s.dsh_conf0) = none &&
                (s.dsh_conf1) =
                  (((ClientID -> Carousel_Client_Reading) +
                      (CoordinatorID ->
                         Carousel_Coordinator_Replicate)) +
                     (PartLdrID ->
                        Carousel_PartitionLeader_Waiting)) &&
                (s.dsh_sc_used0) = none &&
                (s.dsh_taken0) = NO_TRANS &&
                (s.dsh_sc_used1) = (none -> none) &&
                (s.dsh_taken1) = (none -> none) &&
                no
                p1_CoordinatorID.(s.Carousel_Coordinator_client) &&
                no
                p1_CoordinatorID.(s.Carousel_Coordinator_coord_responses) &&
                no
                p1_CoordinatorID.(s.Carousel_Coordinator_info) &&
                no
                p1_CoordinatorID.(s.Carousel_Coordinator_currentTxn) &&
                (all disj p,q: PartLdrID | (p.(s.Carousel_PartitionLeader_data)) =
                                             (q.(s.Carousel_PartitionLeader_data))) &&
                (all disj p,q: PartLdrID | (p.(s.Carousel_PartitionLeader_pendingTxn)) =
                                             (q.(s.Carousel_PartitionLeader_pendingTxn))) &&
                no
                p2_PartLdrID.(s.Carousel_PartitionLeader_response) &&
                one
                p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn) &&
                no
                p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn) &&
                no
                p0_ClientID.(s.Carousel_Client_response) &&
                some
                p0_ClientID.(s.Carousel_Client_data) &&
                no
                p0_ClientID.(s.Carousel_Client_txn))
  (s.dsh_stable).boolean/isTrue
}

pred Carousel_Client_Waiting_FinalizeCommit_pre [
	s: one DshSnapshot,
	p0_ClientID: one ClientID] {
  some
((p0_ClientID -> Carousel_Client_Waiting) & (s.dsh_conf1))
  one
  p0_ClientID.(s.Carousel_Client_response) &&
  Commit in p0_ClientID.(s.Carousel_Client_response)
  !(CarouselScope in (s.dsh_sc_used0))
  !((p0_ClientID -> Carousel_ClientScope) in (s.dsh_sc_used1))
}


pred Carousel_Client_Waiting_FinalizeCommit_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_ClientID -> Carousel_Client_Reading) +
         (p0_ClientID -> Carousel_Client_Waiting))) +
     (p0_ClientID -> Carousel_Client_Reading))
  (p0_ClientID.(sn.Carousel_Client_data)) =
  ((p0_ClientID.(s.Carousel_Client_txn)).key) &&
  (p0_ClientID.(sn.Carousel_Client_txn)) = none &&
  no
  p0_ClientID.(sn.Carousel_Client_response)
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_ClientID -> Carousel_Client_Waiting_FinalizeCommit)
  (all ClientID_aa: ClientID - p0_ClientID | (ClientID_aa.(s.Carousel_Client_data)) =
                                             (ClientID_aa.(sn.Carousel_Client_data)))
  (all ClientID_aa: ClientID - p0_ClientID | (ClientID_aa.(s.Carousel_Client_txn)) =
                                             (ClientID_aa.(sn.Carousel_Client_txn)))
  (all ClientID_aa: ClientID - p0_ClientID | (ClientID_aa.(s.Carousel_Client_response)) =
                                             (ClientID_aa.(sn.Carousel_Client_response)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_pendingTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_pendingTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_transToSend)) =
               (ClientID_aa.(sn.Carousel_Client_transToSend)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_coord_responses)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_coord_responses)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_client)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_client)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_currentTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_currentTxn)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_info)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_info)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_data)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_currentTxn)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_currentTxn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_response)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_response)))
  {((p0_ClientID -> Carousel_Client).(none.(none.(none.(p0_ClientID.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_ClientID -> Carousel_ClientScope)))}
       )}

}

pred Carousel_Client_Waiting_FinalizeCommit_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_ClientID -> Carousel_Client_Waiting) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(Carousel in sc0) &&
    !((p0_ClientID -> Carousel_Client) in sc1) ||
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
  !(CarouselScope in (s.dsh_sc_used0))
  !((p2_PartLdrID -> Carousel_PartitionLeaderScope) in
    (s.dsh_sc_used1))
}


pred Carousel_PartitionLeader_Abort_AbortTransaction_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) +
          (p2_PartLdrID -> Carousel_PartitionLeader_Commit)) +
         (p2_PartLdrID -> Carousel_PartitionLeader_Abort))) +
     (p2_PartLdrID -> Carousel_PartitionLeader_Waiting))
  (p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).removeFirst) &&
  ((((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).firstElem).coordinator).(sn.Carousel_Coordinator_coord_responses)) =
    (((((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).firstElem).coordinator).(s.Carousel_Coordinator_coord_responses)) +
       (p2_PartLdrID -> Abort)) &&
  no
  p2_PartLdrID.(sn.Carousel_PartitionLeader_response) &&
  (all others: CoordinatorID -
                 (((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).firstElem).coordinator) | (others.(sn.Carousel_Coordinator_coord_responses)) =
                                                                                                      (others.(s.Carousel_Coordinator_coord_responses)))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p2_PartLdrID ->
     Carousel_PartitionLeader_Abort_AbortTransaction)
  (all PartLdrID_aa: PartLdrID - p2_PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_response)) =
                                                (PartLdrID_aa.(sn.Carousel_PartitionLeader_response)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_pendingTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_pendingTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_transToSend)) =
               (ClientID_aa.(sn.Carousel_Client_transToSend)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_data)) =
               (ClientID_aa.(sn.Carousel_Client_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_client)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_client)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_currentTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_currentTxn)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_info)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_info)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_txn)) =
               (ClientID_aa.(sn.Carousel_Client_txn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_data)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_currentTxn)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_currentTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_response)) =
               (ClientID_aa.(sn.Carousel_Client_response)))
  {((p2_PartLdrID -> Carousel_PartitionLeader).(none.(p2_PartLdrID.(none.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p2_PartLdrID ->
                      Carousel_PartitionLeaderScope)))}
       )}

}

pred Carousel_PartitionLeader_Abort_AbortTransaction_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Abort) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(Carousel in sc0) &&
    !((p2_PartLdrID -> Carousel_PartitionLeader) in sc1) ||
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
  !(CarouselScope in (s.dsh_sc_used0))
  !((p0_ClientID -> Carousel_ClientScope) in (s.dsh_sc_used1))
}


pred Carousel_Client_Reading_ReadAndPrepare_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_ClientID -> Carousel_Client_Reading) +
         (p0_ClientID -> Carousel_Client_Waiting))) +
     (p0_ClientID -> Carousel_Client_Waiting))
  (one t: p0_ClientID.(s.Carousel_Client_transToSend),c: CoordinatorID | (all leader: PartLdrID | (p0_ClientID.(sn.Carousel_Client_txn)) =
                                                                                                  t &&
                                                                                                  (c.(sn.Carousel_Coordinator_client)) =
                                                                                                    p0_ClientID &&
                                                                                                  no
                                                                                                  c.(s.Carousel_Coordinator_currentTxn) &&
                                                                                                  (c.(sn.Carousel_Coordinator_currentTxn)) =
                                                                                                    t &&
                                                                                                  (t.coordinator) =
                                                                                                    c &&
                                                                                                  t.((leader.(sn.Carousel_PartitionLeader_currentTxn)).((leader.(s.Carousel_PartitionLeader_currentTxn)).add)) &&
                                                                                                  (p0_ClientID.(sn.Carousel_Client_transToSend)) =
                                                                                                    ((p0_ClientID.(s.Carousel_Client_transToSend)) -
                                                                                                       t) &&
                                                                                                  (all others: CoordinatorID -
                                                                                                                 c | (others.(sn.Carousel_Coordinator_client)) =
                                                                                                                       (others.(s.Carousel_Coordinator_client))) &&
                                                                                                  (all others: CoordinatorID -
                                                                                                                 c | (others.(sn.Carousel_Coordinator_currentTxn)) =
                                                                                                                       (others.(s.Carousel_Coordinator_currentTxn)))))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_ClientID -> Carousel_Client_Reading_ReadAndPrepare)
  (all ClientID_aa: ClientID - p0_ClientID | (ClientID_aa.(s.Carousel_Client_transToSend)) =
                                             (ClientID_aa.(sn.Carousel_Client_transToSend)))
  (all ClientID_aa: ClientID - p0_ClientID | (ClientID_aa.(s.Carousel_Client_txn)) =
                                             (ClientID_aa.(sn.Carousel_Client_txn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_pendingTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_pendingTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_data)) =
               (ClientID_aa.(sn.Carousel_Client_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_coord_responses)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_coord_responses)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_info)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_info)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_data)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_data)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_response)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_response)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_response)) =
               (ClientID_aa.(sn.Carousel_Client_response)))
  {((p0_ClientID -> Carousel_Client).(none.(none.(none.(p0_ClientID.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_ClientID -> Carousel_ClientScope)))}
       )}

}

pred Carousel_Client_Reading_ReadAndPrepare_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_ClientID -> Carousel_Client_Reading) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(Carousel in sc0) &&
    !((p0_ClientID -> Carousel_Client) in sc1) ||
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
  p1_CoordinatorID.(s.Carousel_Coordinator_coord_responses) &&
  Abort in
    (PartLdrID.(p1_CoordinatorID.(s.Carousel_Coordinator_coord_responses)))
  !(CarouselScope in (s.dsh_sc_used0))
  !((p1_CoordinatorID -> Carousel_CoordinatorScope) in
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
  Abort &&
  (all others: ClientID -
                 (p1_CoordinatorID.(s.Carousel_Coordinator_client)) | (others.(sn.Carousel_Client_response)) =
                                                                        (others.(s.Carousel_Client_response))) &&
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_info) &&
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_currentTxn) &&
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_client) &&
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_coord_responses)
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p1_CoordinatorID ->
     Carousel_Coordinator_WaitForResponse_StartAbort)
  (all CoordinatorID_aa: CoordinatorID - p1_CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_coord_responses)) =
                                                            (CoordinatorID_aa.(sn.Carousel_Coordinator_coord_responses)))
  (all CoordinatorID_aa: CoordinatorID - p1_CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_client)) =
                                                            (CoordinatorID_aa.(sn.Carousel_Coordinator_client)))
  (all CoordinatorID_aa: CoordinatorID - p1_CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_info)) =
                                                            (CoordinatorID_aa.(sn.Carousel_Coordinator_info)))
  (all CoordinatorID_aa: CoordinatorID - p1_CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_currentTxn)) =
                                                            (CoordinatorID_aa.(sn.Carousel_Coordinator_currentTxn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_pendingTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_pendingTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_transToSend)) =
               (ClientID_aa.(sn.Carousel_Client_transToSend)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_data)) =
               (ClientID_aa.(sn.Carousel_Client_data)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_currentTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_currentTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_txn)) =
               (ClientID_aa.(sn.Carousel_Client_txn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_data)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_data)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_response)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_response)))
  {((p1_CoordinatorID -> Carousel_Coordinator).(none.(none.(p1_CoordinatorID.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p1_CoordinatorID ->
                      Carousel_CoordinatorScope)))}
       )}

}

pred Carousel_Coordinator_WaitForResponse_StartAbort_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p1_CoordinatorID -> Carousel_Coordinator_WaitForResponse) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(Carousel in sc0) &&
    !((p1_CoordinatorID -> Carousel_Coordinator) in sc1) ||
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
  ((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).elems) &&
  no
  p2_PartLdrID.(s.Carousel_PartitionLeader_response) &&
  !(((((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).firstElem).key).Value) in
      ((((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).elems).key).Value))
  !(CarouselScope in (s.dsh_sc_used0))
  !((p2_PartLdrID -> Carousel_PartitionLeaderScope) in
    (s.dsh_sc_used1))
}


pred Carousel_PartitionLeader_Waiting_PrepareCommit_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) +
          (p2_PartLdrID -> Carousel_PartitionLeader_Commit)) +
         (p2_PartLdrID -> Carousel_PartitionLeader_Abort))) +
     (p2_PartLdrID -> Carousel_PartitionLeader_Commit))
  ((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).firstElem).((p2_PartLdrID.(sn.Carousel_PartitionLeader_pendingTxn)).((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).add)) &&
  (p2_PartLdrID.(sn.Carousel_PartitionLeader_currentTxn)).((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).removeFirst)
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p2_PartLdrID ->
     Carousel_PartitionLeader_Waiting_PrepareCommit)
  (all PartLdrID_aa: PartLdrID - p2_PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_pendingTxn)) =
                                                (PartLdrID_aa.(sn.Carousel_PartitionLeader_pendingTxn)))
  (all PartLdrID_aa: PartLdrID - p2_PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_currentTxn)) =
                                                (PartLdrID_aa.(sn.Carousel_PartitionLeader_currentTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_transToSend)) =
               (ClientID_aa.(sn.Carousel_Client_transToSend)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_data)) =
               (ClientID_aa.(sn.Carousel_Client_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_coord_responses)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_coord_responses)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_client)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_client)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_info)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_info)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_txn)) =
               (ClientID_aa.(sn.Carousel_Client_txn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_data)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_currentTxn)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_currentTxn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_response)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_response)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_response)) =
               (ClientID_aa.(sn.Carousel_Client_response)))
  {((p2_PartLdrID -> Carousel_PartitionLeader).(none.(p2_PartLdrID.(none.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p2_PartLdrID ->
                      Carousel_PartitionLeaderScope)))}
       )}

}

pred Carousel_PartitionLeader_Waiting_PrepareCommit_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(Carousel in sc0) &&
    !((p2_PartLdrID -> Carousel_PartitionLeader) in sc1) ||
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
  (# PartLdrID) &&
  !(Abort in
      (PartLdrID.(p1_CoordinatorID.(s.Carousel_Coordinator_coord_responses))))
  !(CarouselScope in (s.dsh_sc_used0))
  !((p1_CoordinatorID -> Carousel_CoordinatorScope) in
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
  Commit &&
  (all others: ClientID -
                 (p1_CoordinatorID.(s.Carousel_Coordinator_client)) | (others.(sn.Carousel_Client_response)) =
                                                                        (others.(s.Carousel_Client_response))) &&
  (all leader: PartLdrID | (leader.(sn.Carousel_PartitionLeader_response)) =
                             (p1_CoordinatorID.(s.Carousel_Coordinator_currentTxn) ->
                                Commit)) &&
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_info) &&
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_currentTxn) &&
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_client) &&
  no
  p1_CoordinatorID.(sn.Carousel_Coordinator_coord_responses)
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p1_CoordinatorID ->
     Carousel_Coordinator_WaitForResponse_StartCommit)
  (all CoordinatorID_aa: CoordinatorID - p1_CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_coord_responses)) =
                                                            (CoordinatorID_aa.(sn.Carousel_Coordinator_coord_responses)))
  (all CoordinatorID_aa: CoordinatorID - p1_CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_client)) =
                                                            (CoordinatorID_aa.(sn.Carousel_Coordinator_client)))
  (all CoordinatorID_aa: CoordinatorID - p1_CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_info)) =
                                                            (CoordinatorID_aa.(sn.Carousel_Coordinator_info)))
  (all CoordinatorID_aa: CoordinatorID - p1_CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_currentTxn)) =
                                                            (CoordinatorID_aa.(sn.Carousel_Coordinator_currentTxn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_pendingTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_pendingTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_transToSend)) =
               (ClientID_aa.(sn.Carousel_Client_transToSend)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_data)) =
               (ClientID_aa.(sn.Carousel_Client_data)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_currentTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_currentTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_txn)) =
               (ClientID_aa.(sn.Carousel_Client_txn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_data)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_data)))
  {((p1_CoordinatorID -> Carousel_Coordinator).(none.(none.(p1_CoordinatorID.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p1_CoordinatorID ->
                      Carousel_CoordinatorScope)))}
       )}

}

pred Carousel_Coordinator_WaitForResponse_StartCommit_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p1_CoordinatorID -> Carousel_Coordinator_WaitForResponse) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(Carousel in sc0) &&
    !((p1_CoordinatorID -> Carousel_Coordinator) in sc1) ||
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
  p0_ClientID.(s.Carousel_Client_response) &&
  Abort in p0_ClientID.(s.Carousel_Client_response)
  !(CarouselScope in (s.dsh_sc_used0))
  !((p0_ClientID -> Carousel_ClientScope) in (s.dsh_sc_used1))
}


pred Carousel_Client_Waiting_FinalizeAbort_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_ClientID -> Carousel_Client_Reading) +
         (p0_ClientID -> Carousel_Client_Waiting))) +
     (p0_ClientID -> Carousel_Client_Reading))
  (p0_ClientID.(sn.Carousel_Client_txn)) = none &&
  no
  p0_ClientID.(sn.Carousel_Client_response)
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_ClientID -> Carousel_Client_Waiting_FinalizeAbort)
  (all ClientID_aa: ClientID - p0_ClientID | (ClientID_aa.(s.Carousel_Client_txn)) =
                                             (ClientID_aa.(sn.Carousel_Client_txn)))
  (all ClientID_aa: ClientID - p0_ClientID | (ClientID_aa.(s.Carousel_Client_response)) =
                                             (ClientID_aa.(sn.Carousel_Client_response)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_pendingTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_pendingTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_transToSend)) =
               (ClientID_aa.(sn.Carousel_Client_transToSend)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_data)) =
               (ClientID_aa.(sn.Carousel_Client_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_coord_responses)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_coord_responses)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_client)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_client)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_currentTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_currentTxn)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_info)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_info)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_data)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_currentTxn)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_currentTxn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_response)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_response)))
  {((p0_ClientID -> Carousel_Client).(none.(none.(none.(p0_ClientID.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_ClientID -> Carousel_ClientScope)))}
       )}

}

pred Carousel_Client_Waiting_FinalizeAbort_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p0_ClientID -> Carousel_Client_Waiting) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(Carousel in sc0) &&
    !((p0_ClientID -> Carousel_Client) in sc1) ||
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
  !(CarouselScope in (s.dsh_sc_used0))
  !((p2_PartLdrID -> Carousel_PartitionLeaderScope) in
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
  p2_PartLdrID.(sn.Carousel_PartitionLeader_response) &&
  (p2_PartLdrID.(sn.Carousel_PartitionLeader_pendingTxn)).((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).removeFirst) &&
  (p2_PartLdrID.(sn.Carousel_PartitionLeader_data)) =
    (p2_PartLdrID.(s.Carousel_PartitionLeader_data) ++
       (((p2_PartLdrID.(s.Carousel_PartitionLeader_response)).Response).key))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p2_PartLdrID ->
     Carousel_PartitionLeader_Waiting_FinalizeCommit)
  (all PartLdrID_aa: PartLdrID - p2_PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_pendingTxn)) =
                                                (PartLdrID_aa.(sn.Carousel_PartitionLeader_pendingTxn)))
  (all PartLdrID_aa: PartLdrID - p2_PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_data)) =
                                                (PartLdrID_aa.(sn.Carousel_PartitionLeader_data)))
  (all PartLdrID_aa: PartLdrID - p2_PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_response)) =
                                                (PartLdrID_aa.(sn.Carousel_PartitionLeader_response)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_transToSend)) =
               (ClientID_aa.(sn.Carousel_Client_transToSend)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_data)) =
               (ClientID_aa.(sn.Carousel_Client_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_coord_responses)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_coord_responses)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_client)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_client)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_currentTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_currentTxn)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_info)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_info)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_txn)) =
               (ClientID_aa.(sn.Carousel_Client_txn)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_currentTxn)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_currentTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_response)) =
               (ClientID_aa.(sn.Carousel_Client_response)))
  {((p2_PartLdrID -> Carousel_PartitionLeader).(none.(p2_PartLdrID.(none.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p2_PartLdrID ->
                      Carousel_PartitionLeaderScope)))}
       )}

}

pred Carousel_PartitionLeader_Waiting_FinalizeCommit_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(Carousel in sc0) &&
    !((p2_PartLdrID -> Carousel_PartitionLeader) in sc1) ||
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
  ((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).elems) &&
  ((((p2_PartLdrID.(s.Carousel_PartitionLeader_currentTxn)).firstElem).key).Value) in
    ((((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).elems).key).Value)
  !(CarouselScope in (s.dsh_sc_used0))
  !((p2_PartLdrID -> Carousel_PartitionLeaderScope) in
    (s.dsh_sc_used1))
}


pred Carousel_PartitionLeader_Waiting_PrepareAbort_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) +
          (p2_PartLdrID -> Carousel_PartitionLeader_Commit)) +
         (p2_PartLdrID -> Carousel_PartitionLeader_Abort))) +
     (p2_PartLdrID -> Carousel_PartitionLeader_Abort))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p2_PartLdrID ->
     Carousel_PartitionLeader_Waiting_PrepareAbort)
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_pendingTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_pendingTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_transToSend)) =
               (ClientID_aa.(sn.Carousel_Client_transToSend)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_data)) =
               (ClientID_aa.(sn.Carousel_Client_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_coord_responses)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_coord_responses)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_client)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_client)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_currentTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_currentTxn)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_info)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_info)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_txn)) =
               (ClientID_aa.(sn.Carousel_Client_txn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_data)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_currentTxn)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_currentTxn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_response)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_response)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_response)) =
               (ClientID_aa.(sn.Carousel_Client_response)))
  {((p2_PartLdrID -> Carousel_PartitionLeader).(none.(p2_PartLdrID.(none.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p2_PartLdrID ->
                      Carousel_PartitionLeaderScope)))}
       )}

}

pred Carousel_PartitionLeader_Waiting_PrepareAbort_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(Carousel in sc0) &&
    !((p2_PartLdrID -> Carousel_PartitionLeader) in sc1) ||
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
  !(CarouselScope in (s.dsh_sc_used0))
  !((p1_CoordinatorID -> Carousel_CoordinatorScope) in
    (s.dsh_sc_used1))
}


pred Carousel_Coordinator_Replicate_Replicating_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p1_CoordinatorID -> Carousel_Coordinator_Replicate) +
         (p1_CoordinatorID ->
            Carousel_Coordinator_WaitForResponse))) +
     (p1_CoordinatorID ->
        Carousel_Coordinator_WaitForResponse))
  (p1_CoordinatorID.(sn.Carousel_Coordinator_info)) =
  ((p1_CoordinatorID.(s.Carousel_Coordinator_currentTxn)).key)
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p1_CoordinatorID ->
     Carousel_Coordinator_Replicate_Replicating)
  (all CoordinatorID_aa: CoordinatorID - p1_CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_info)) =
                                                            (CoordinatorID_aa.(sn.Carousel_Coordinator_info)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_pendingTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_pendingTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_transToSend)) =
               (ClientID_aa.(sn.Carousel_Client_transToSend)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_data)) =
               (ClientID_aa.(sn.Carousel_Client_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_coord_responses)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_coord_responses)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_client)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_client)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_currentTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_currentTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_txn)) =
               (ClientID_aa.(sn.Carousel_Client_txn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_data)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_currentTxn)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_currentTxn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_response)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_response)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_response)) =
               (ClientID_aa.(sn.Carousel_Client_response)))
  {((p1_CoordinatorID -> Carousel_Coordinator).(none.(none.(p1_CoordinatorID.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p1_CoordinatorID ->
                      Carousel_CoordinatorScope)))}
       )}

}

pred Carousel_Coordinator_Replicate_Replicating_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p1_CoordinatorID: one CoordinatorID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p1_CoordinatorID -> Carousel_Coordinator_Replicate) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(Carousel in sc0) &&
    !((p1_CoordinatorID -> Carousel_Coordinator) in sc1) ||
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
  !(CarouselScope in (s.dsh_sc_used0))
  !((p2_PartLdrID -> Carousel_PartitionLeaderScope) in
    (s.dsh_sc_used1))
}


pred Carousel_PartitionLeader_Commit_CommitTransaction_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (((p2_PartLdrID -> Carousel_PartitionLeader_Waiting) +
          (p2_PartLdrID -> Carousel_PartitionLeader_Commit)) +
         (p2_PartLdrID -> Carousel_PartitionLeader_Abort))) +
     (p2_PartLdrID -> Carousel_PartitionLeader_Waiting))
  ((((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).firstElem).coordinator).(sn.Carousel_Coordinator_coord_responses)) =
  (((((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).firstElem).coordinator).(s.Carousel_Coordinator_coord_responses)) +
     (p2_PartLdrID -> Commit)) &&
  (all others: CoordinatorID -
                 (((p2_PartLdrID.(s.Carousel_PartitionLeader_pendingTxn)).firstElem).coordinator) | (others.(sn.Carousel_Coordinator_coord_responses)) =
                                                                                                      (others.(s.Carousel_Coordinator_coord_responses)))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p2_PartLdrID ->
     Carousel_PartitionLeader_Commit_CommitTransaction)
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_pendingTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_pendingTxn)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_transToSend)) =
               (ClientID_aa.(sn.Carousel_Client_transToSend)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_data)) =
               (ClientID_aa.(sn.Carousel_Client_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_client)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_client)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_currentTxn)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_currentTxn)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_info)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_info)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_txn)) =
               (ClientID_aa.(sn.Carousel_Client_txn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_data)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_data)))
  (all CoordinatorID_aa: one
  CoordinatorID | (CoordinatorID_aa.(s.Carousel_Coordinator_currentTxn)) =
                    (CoordinatorID_aa.(sn.Carousel_Coordinator_currentTxn)))
  (all PartLdrID_aa: one
  PartLdrID | (PartLdrID_aa.(s.Carousel_PartitionLeader_response)) =
                (PartLdrID_aa.(sn.Carousel_PartitionLeader_response)))
  (all ClientID_aa: one
  ClientID | (ClientID_aa.(s.Carousel_Client_response)) =
               (ClientID_aa.(sn.Carousel_Client_response)))
  {((p2_PartLdrID -> Carousel_PartitionLeader).(none.(p2_PartLdrID.(none.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       { (s.dsh_stable).boolean/isTrue ||
           !((s.dsh_stable).boolean/isTrue) })
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           ((sn.dsh_sc_used0) = none &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p2_PartLdrID ->
                      Carousel_PartitionLeaderScope)))}
       )}

}

pred Carousel_PartitionLeader_Commit_CommitTransaction_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some
((p2_PartLdrID -> Carousel_PartitionLeader_Commit) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(Carousel in sc0) &&
    !((p2_PartLdrID -> Carousel_PartitionLeader) in sc1) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred Carousel_PartitionLeader_Commit_CommitTransaction [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p2_PartLdrID: one PartLdrID] {
  p2_PartLdrID.(s.Carousel_PartitionLeader_Commit_CommitTransaction_pre)
  p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Commit_CommitTransaction_post))
}

pred _nextIsStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_ClientID: one ClientID,
	p1_CoordinatorID: one CoordinatorID,
	p2_PartLdrID: one PartLdrID,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  !(sc1.(sc0.(p0_ClientID.(sn.(s.Carousel_Client_Waiting_FinalizeCommit_enabledAfterStep)))))
  !(sc1.(sc0.(p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Abort_AbortTransaction_enabledAfterStep)))))
  !(sc1.(sc0.(p0_ClientID.(sn.(s.Carousel_Client_Reading_ReadAndPrepare_enabledAfterStep)))))
  !(sc1.(sc0.(p1_CoordinatorID.(sn.(s.Carousel_Coordinator_WaitForResponse_StartAbort_enabledAfterStep)))))
  !(sc1.(sc0.(p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_PrepareCommit_enabledAfterStep)))))
  !(sc1.(sc0.(p1_CoordinatorID.(sn.(s.Carousel_Coordinator_WaitForResponse_StartCommit_enabledAfterStep)))))
  !(sc1.(sc0.(p0_ClientID.(sn.(s.Carousel_Client_Waiting_FinalizeAbort_enabledAfterStep)))))
  !(sc1.(sc0.(p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_FinalizeCommit_enabledAfterStep)))))
  !(sc1.(sc0.(p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_PrepareAbort_enabledAfterStep)))))
  !(sc1.(sc0.(p1_CoordinatorID.(sn.(s.Carousel_Coordinator_Replicate_Replicating_enabledAfterStep)))))
  !(sc1.(sc0.(p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Commit_CommitTransaction_enabledAfterStep)))))
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_stable) = (s.dsh_stable)
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_sc_used0) = (s.dsh_sc_used0)
  (sn.dsh_taken0) = NO_TRANS
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.dsh_sc_used1) = (s.dsh_sc_used1)
  (sn.dsh_taken1) = (none -> none)
  (sn.Carousel_Client_response) = (s.Carousel_Client_response)
  (sn.Carousel_Client_data) = (s.Carousel_Client_data)
  (sn.Carousel_Client_txn) = (s.Carousel_Client_txn)
  (sn.Carousel_Client_transToSend) =
  (s.Carousel_Client_transToSend)
  (sn.Carousel_Coordinator_currentTxn) =
  (s.Carousel_Coordinator_currentTxn)
  (sn.Carousel_Coordinator_client) =
  (s.Carousel_Coordinator_client)
  (sn.Carousel_Coordinator_info) =
  (s.Carousel_Coordinator_info)
  (sn.Carousel_Coordinator_coord_responses) =
  (s.Carousel_Coordinator_coord_responses)
  (sn.Carousel_PartitionLeader_response) =
  (s.Carousel_PartitionLeader_response)
  (sn.Carousel_PartitionLeader_data) =
  (s.Carousel_PartitionLeader_data)
  (sn.Carousel_PartitionLeader_currentTxn) =
  (s.Carousel_PartitionLeader_currentTxn)
  (sn.Carousel_PartitionLeader_pendingTxn) =
  (s.Carousel_PartitionLeader_pendingTxn)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { (some p0_ClientID: one
      ClientID,p1_CoordinatorID: one
      CoordinatorID,p2_PartLdrID: one
      PartLdrID | { p0_ClientID.(sn.(s.Carousel_Client_Waiting_FinalizeCommit)) ||
                      p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Abort_AbortTransaction)) ||
                      p0_ClientID.(sn.(s.Carousel_Client_Reading_ReadAndPrepare)) ||
                      p1_CoordinatorID.(sn.(s.Carousel_Coordinator_WaitForResponse_StartAbort)) ||
                      p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_PrepareCommit)) ||
                      p1_CoordinatorID.(sn.(s.Carousel_Coordinator_WaitForResponse_StartCommit)) ||
                      p0_ClientID.(sn.(s.Carousel_Client_Waiting_FinalizeAbort)) ||
                      p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_FinalizeCommit)) ||
                      p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Waiting_PrepareAbort)) ||
                      p1_CoordinatorID.(sn.(s.Carousel_Coordinator_Replicate_Replicating)) ||
                      p2_PartLdrID.(sn.(s.Carousel_PartitionLeader_Commit_CommitTransaction)) }) ||
    !((some p0_ClientID: one
         ClientID,p1_CoordinatorID: one
         CoordinatorID,p2_PartLdrID: one
         PartLdrID | { p0_ClientID.(s.Carousel_Client_Waiting_FinalizeCommit_pre) ||
                         p2_PartLdrID.(s.Carousel_PartitionLeader_Abort_AbortTransaction_pre) ||
                         p0_ClientID.(s.Carousel_Client_Reading_ReadAndPrepare_pre) ||
                         p1_CoordinatorID.(s.Carousel_Coordinator_WaitForResponse_StartAbort_pre) ||
                         p2_PartLdrID.(s.Carousel_PartitionLeader_Waiting_PrepareCommit_pre) ||
                         p1_CoordinatorID.(s.Carousel_Coordinator_WaitForResponse_StartCommit_pre) ||
                         p0_ClientID.(s.Carousel_Client_Waiting_FinalizeAbort_pre) ||
                         p2_PartLdrID.(s.Carousel_PartitionLeader_Waiting_FinalizeCommit_pre) ||
                         p2_PartLdrID.(s.Carousel_PartitionLeader_Waiting_PrepareAbort_pre) ||
                         p1_CoordinatorID.(s.Carousel_Coordinator_Replicate_Replicating_pre) ||
                         p2_PartLdrID.(s.Carousel_PartitionLeader_Commit_CommitTransaction_pre) })) &&
      sn.(s.dsh_stutter) }
}

fact dsh_complete_big_steps {
  (all s: one
  DshSnapshot | ((s.dsh_stable).boolean/isFalse) =>
                  ((some sn: one
                      DshSnapshot | sn.(s.dsh_small_step))))
}

fact allSnapshotsDifferent {
  (all s: one
  DshSnapshot,sn: one
  DshSnapshot | ((s.dsh_conf0) = (sn.dsh_conf0) &&
                   (s.dsh_sc_used0) = (sn.dsh_sc_used0) &&
                   (s.dsh_taken0) = (sn.dsh_taken0) &&
                   (s.dsh_conf1) = (sn.dsh_conf1) &&
                   (s.dsh_sc_used1) = (sn.dsh_sc_used1) &&
                   (s.dsh_taken1) = (sn.dsh_taken1) &&
                   (s.dsh_stable) = (sn.dsh_stable)) =>
                  (s = sn))
}

fact dsh_tcmc_fact {
  (all s: one
  DshSnapshot | (s in tcmc/ks_s0) <=> (s.dsh_initial))
  (all s: one
  DshSnapshot,sn: one
  DshSnapshot | ((s -> sn) in tcmc/ks_sigma) <=>
                  (sn.(s.dsh_small_step)))
}

