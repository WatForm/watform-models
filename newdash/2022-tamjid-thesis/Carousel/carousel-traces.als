/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-05-18 09:59:24
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
sig PartLdrID extends DshIds {} 
sig ClientID extends DshIds {} 
sig CoordinatorID extends DshIds {} 

sig bufIdx0 {}
sig bufIdx1 {}
sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_sc_used1: DshIds -> DshStates,
  dsh_conf1: DshIds -> DshStates,
  dsh_stable: one boolean/Bool,
  Carousel_Client_transToSend: ClientID -> set Transaction,
  Carousel_Client_data: ClientID -> (Key ->one Value),
  Carousel_Coordinator_coord_responses: CoordinatorID ->
                                        (PartLdrID ->one
                                           Response),
  Carousel_Coordinator_client: CoordinatorID -> lone ClientID,
  Carousel_Coordinator_info: CoordinatorID ->
                             (Key ->one Value),
  Carousel_Client_txn: ClientID -> lone Transaction,
  Carousel_PartitionLeader_data: PartLdrID ->
                                 (Key ->one Value),
  Carousel_Coordinator_currentTxn: CoordinatorID -> lone
                                   Transaction,
  Carousel_PartitionLeader_response: PartLdrID ->
                                     (Transaction ->one
                                        Response),
  Carousel_Client_response: ClientID -> lone Response,
  Carousel_PartitionLeader_pendingTxn: PartLdrID ->
                                       (bufIdx1 ->
                                          Transaction),
  Carousel_PartitionLeader_currentTxn: PartLdrID ->
                                       (bufIdx0 ->
                                          Transaction)
}

pred dsh_initial [s: one DshSnapshot, pPartLdrID: one PartLdrID, pClientID: one ClientID, pCoordinatorID: one CoordinatorID] {
  (all pPartLdrID: one
  PartLdrID,pClientID: one
  ClientID,pCoordinatorID: one
  CoordinatorID | no
                    (pCoordinatorID .
                       (s . Carousel_Coordinator_client)) and
                    no
                    (pCoordinatorID .
                       (s .
                          Carousel_Coordinator_coord_responses)) and
                    no
                    (pCoordinatorID .
                       (s . Carousel_Coordinator_info)) and
                    no
                    (pCoordinatorID .
                       (s . Carousel_Coordinator_currentTxn)) and
                    (all disj p,q: PartLdrID | (p.(pPartLdrID
                                                     .
                                                     (s .
                                                        Carousel_PartitionLeader_data)))
                                                 =
                                                 (q.(pPartLdrID
                                                       .
                                                       (s .
                                                          Carousel_PartitionLeader_data)))) and
                    (all disj p,q: PartLdrID | (p.(pPartLdrID
                                                     .
                                                     (s .
                                                        Carousel_PartitionLeader_pendingTxn)))
                                                 =
                                                 (q.(pPartLdrID
                                                       .
                                                       (s .
                                                          Carousel_PartitionLeader_pendingTxn)))) and
                    no
                    (pPartLdrID .
                       (s .
                          Carousel_PartitionLeader_response)) and
                    one
                    (pPartLdrID .
                       (s .
                          Carousel_PartitionLeader_pendingTxn)) and
                    no
                    (pPartLdrID .
                       (s .
                          Carousel_PartitionLeader_currentTxn)) and
                    no
                    (pClientID .
                       (s . Carousel_Client_response)) and
                    some
                    (pClientID . (s . Carousel_Client_data)) and
                    no
                    (pClientID . (s . Carousel_Client_txn)) and
                    (#
                      (pClientID .
                         (s . Carousel_Client_transToSend)))
                      = (2))
}

pred Carousel_Client_Waiting_FinalizeCommit_pre [s: one DshSnapshot, pClientID: one ClientID] {
  some
((pClientID -> Carousel_Client_Waiting) & (s . dsh_conf1))
  one
  (pClientID . (s . Carousel_Client_response)) and
  Commit in (pClientID . (s . Carousel_Client_response))
  ! (Carousel in (s . dsh_sc_used0))
  ! ((pClientID -> Carousel_Client) in (s . dsh_sc_used1))
}


pred Carousel_Client_Waiting_FinalizeCommit_post [s: one DshSnapshot, sn: one DshSnapshot, pClientID: one ClientID] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) - (pClientID -> Carousel_Client_Reading))
     + (pClientID -> Carousel_Client_Reading))
  (pClientID . (sn . Carousel_Client_data)) =
  ((pClientID . (s . Carousel_Client_txn)).key) and
  (pClientID . (sn . Carousel_Client_txn)) = none and
  no
  (pClientID . (sn . Carousel_Client_response))
  ((pClientID -> Carousel_Client) .
   (none . (sn . (s . _testIfNextStable))))=>
    ((sn . dsh_stable) = boolean/True and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })

}

pred Carousel_Client_Waiting_FinalizeCommit_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pClientID: one ClientID, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pClientID -> Carousel_Client_Waiting) & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (Carousel in dsh_scp0) and
    !
    ((pClientID -> Carousel_Client) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred Carousel_Client_Waiting_FinalizeCommit [s: one DshSnapshot, sn: one DshSnapshot, pClientID: one ClientID] {
  pClientID . (s . Carousel_Client_Waiting_FinalizeCommit_pre)
  pClientID .
  (sn . (s . Carousel_Client_Waiting_FinalizeCommit_post))
}

pred Carousel_PartitionLeader_Abort_AbortTransaction_pre [s: one DshSnapshot, pPartLdrID: one PartLdrID] {
  some
((pPartLdrID -> Carousel_PartitionLeader_Abort) &
   (s . dsh_conf1))
  ! (Carousel in (s . dsh_sc_used0))
  !
((pPartLdrID -> Carousel_PartitionLeader) in
   (s . dsh_sc_used1))
}


pred Carousel_PartitionLeader_Abort_AbortTransaction_post [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pPartLdrID -> Carousel_PartitionLeader_Waiting)) +
     (pPartLdrID -> Carousel_PartitionLeader_Waiting))
  (pPartLdrID . (s . Carousel_PartitionLeader_currentTxn)).removeFirst and
  ((((pPartLdrID . (s . Carousel_PartitionLeader_currentTxn)).firstElem).coordinator)
     . (sn . Carousel_Coordinator_coord_responses)) =
    (((((pPartLdrID .
           (s . Carousel_PartitionLeader_currentTxn)).firstElem).coordinator)
        . (s . Carousel_Coordinator_coord_responses)) +
       (pPartLdrID -> Abort)) and
  no
  (pPartLdrID . (sn . Carousel_PartitionLeader_response)) and
  (all others: CoordinatorID -
                 (((pPartLdrID .
                      (s .
                         Carousel_PartitionLeader_pendingTxn)).firstElem).coordinator) | (others
                                                                                            .
                                                                                            (sn
                                                                                               .
                                                                                               Carousel_Coordinator_coord_responses))
                                                                                           =
                                                                                           (others
                                                                                              .
                                                                                              (s
                                                                                                 .
                                                                                                 Carousel_Coordinator_coord_responses)))
  ((pPartLdrID -> Carousel_PartitionLeader) .
   (none . (sn . (s . _testIfNextStable))))=>
    ((sn . dsh_stable) = boolean/True and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })

}

pred Carousel_PartitionLeader_Abort_AbortTransaction_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pPartLdrID -> Carousel_PartitionLeader_Abort) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (Carousel in dsh_scp0) and
    !
    ((pPartLdrID -> Carousel_PartitionLeader) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred Carousel_PartitionLeader_Abort_AbortTransaction [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID] {
  pPartLdrID .
  (s . Carousel_PartitionLeader_Abort_AbortTransaction_pre)
  pPartLdrID .
  (sn .
     (s .
        Carousel_PartitionLeader_Abort_AbortTransaction_post))
}

pred Carousel_Client_Reading_ReadAndPrepare_pre [s: one DshSnapshot, pClientID: one ClientID] {
  some
((pClientID -> Carousel_Client_Reading) & (s . dsh_conf1))
  (some c: CoordinatorID | no
  (c . (s . Carousel_Coordinator_currentTxn)))
  ! (Carousel in (s . dsh_sc_used0))
  ! ((pClientID -> Carousel_Client) in (s . dsh_sc_used1))
}


pred Carousel_Client_Reading_ReadAndPrepare_post [s: one DshSnapshot, sn: one DshSnapshot, pClientID: one ClientID] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) - (pClientID -> Carousel_Client_Waiting))
     + (pClientID -> Carousel_Client_Waiting))
  (one t: pClientID . (s . Carousel_Client_transToSend),c: CoordinatorID | (all leader: PartLdrID | (pClientID
                                                                                                     .
                                                                                                     (sn
                                                                                                        .
                                                                                                        Carousel_Client_txn))
                                                                                                    =
                                                                                                    t and
                                                                                                    (c
                                                                                                       .
                                                                                                       (sn
                                                                                                          .
                                                                                                          Carousel_Coordinator_client))
                                                                                                      =
                                                                                                      pClientID and
                                                                                                    no
                                                                                                    (c
                                                                                                       .
                                                                                                       (s
                                                                                                          .
                                                                                                          Carousel_Coordinator_currentTxn)) and
                                                                                                    (c
                                                                                                       .
                                                                                                       (sn
                                                                                                          .
                                                                                                          Carousel_Coordinator_currentTxn))
                                                                                                      =
                                                                                                      t and
                                                                                                    (t.coordinator)
                                                                                                      =
                                                                                                      c and
                                                                                                    t.((leader
                                                                                                          .
                                                                                                          (s
                                                                                                             .
                                                                                                             Carousel_PartitionLeader_currentTxn)).add) and
                                                                                                    (pClientID
                                                                                                       .
                                                                                                       (sn
                                                                                                          .
                                                                                                          Carousel_Client_transToSend))
                                                                                                      =
                                                                                                      ((pClientID
                                                                                                          .
                                                                                                          (s
                                                                                                             .
                                                                                                             Carousel_Client_transToSend))
                                                                                                         -
                                                                                                         t) and
                                                                                                    (all others: CoordinatorID
                                                                                                                   -
                                                                                                                   c | (others
                                                                                                                          .
                                                                                                                          (sn
                                                                                                                             .
                                                                                                                             Carousel_Coordinator_client))
                                                                                                                         =
                                                                                                                         (others
                                                                                                                            .
                                                                                                                            (s
                                                                                                                               .
                                                                                                                               Carousel_Coordinator_client))) and
                                                                                                    (all others: CoordinatorID
                                                                                                                   -
                                                                                                                   c | (others
                                                                                                                          .
                                                                                                                          (sn
                                                                                                                             .
                                                                                                                             Carousel_Coordinator_currentTxn))
                                                                                                                         =
                                                                                                                         (others
                                                                                                                            .
                                                                                                                            (s
                                                                                                                               .
                                                                                                                               Carousel_Coordinator_currentTxn)))))
  ((pClientID -> Carousel_Client) .
   (none . (sn . (s . _testIfNextStable))))=>
    ((sn . dsh_stable) = boolean/True and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })

}

pred Carousel_Client_Reading_ReadAndPrepare_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pClientID: one ClientID, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pClientID -> Carousel_Client_Reading) & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (Carousel in dsh_scp0) and
    !
    ((pClientID -> Carousel_Client) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred Carousel_Client_Reading_ReadAndPrepare [s: one DshSnapshot, sn: one DshSnapshot, pClientID: one ClientID] {
  pClientID . (s . Carousel_Client_Reading_ReadAndPrepare_pre)
  pClientID .
  (sn . (s . Carousel_Client_Reading_ReadAndPrepare_post))
}

pred Carousel_Coordinator_WaitForResponse_StartAbort_pre [s: one DshSnapshot, pCoordinatorID: one CoordinatorID] {
  some
((pCoordinatorID -> Carousel_Coordinator_WaitForResponse) &
   (s . dsh_conf1))
  some
  (pCoordinatorID .
     (s . Carousel_Coordinator_coord_responses)) and
  Abort in
    (PartLdrID.(pCoordinatorID .
                  (s . Carousel_Coordinator_coord_responses)))
  ! (Carousel in (s . dsh_sc_used0))
  !
((pCoordinatorID -> Carousel_Coordinator) in
   (s . dsh_sc_used1))
}


pred Carousel_Coordinator_WaitForResponse_StartAbort_post [s: one DshSnapshot, sn: one DshSnapshot, pCoordinatorID: one CoordinatorID] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pCoordinatorID ->
         Carousel_Coordinator_WaitForResponse)) +
     (pCoordinatorID -> Carousel_Coordinator_WaitForResponse))
  ((pCoordinatorID . (s . Carousel_Coordinator_client)) .
   (sn . Carousel_Client_response)) = Abort and
  (all others: ClientID -
                 (pCoordinatorID .
                    (s . Carousel_Coordinator_client)) | (others
                                                            .
                                                            (sn
                                                               .
                                                               Carousel_Client_response))
                                                           =
                                                           (others
                                                              .
                                                              (s
                                                                 .
                                                                 Carousel_Client_response))) and
  no
  (pCoordinatorID . (sn . Carousel_Coordinator_info)) and
  no
  (pCoordinatorID . (sn . Carousel_Coordinator_currentTxn)) and
  no
  (pCoordinatorID . (sn . Carousel_Coordinator_client)) and
  no
  (pCoordinatorID .
     (sn . Carousel_Coordinator_coord_responses))
  ((pCoordinatorID -> Carousel_Coordinator) .
   (none . (sn . (s . _testIfNextStable))))=>
    ((sn . dsh_stable) = boolean/True and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })

}

pred Carousel_Coordinator_WaitForResponse_StartAbort_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pCoordinatorID: one CoordinatorID, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pCoordinatorID -> Carousel_Coordinator_WaitForResponse) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (Carousel in dsh_scp0) and
    !
    ((pCoordinatorID -> Carousel_Coordinator) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred Carousel_Coordinator_WaitForResponse_StartAbort [s: one DshSnapshot, sn: one DshSnapshot, pCoordinatorID: one CoordinatorID] {
  pCoordinatorID .
  (s . Carousel_Coordinator_WaitForResponse_StartAbort_pre)
  pCoordinatorID .
  (sn .
     (s .
        Carousel_Coordinator_WaitForResponse_StartAbort_post))
}

pred Carousel_PartitionLeader_Waiting_PrepareCommit_pre [s: one DshSnapshot, pPartLdrID: one PartLdrID] {
  some
((pPartLdrID -> Carousel_PartitionLeader_Waiting) &
   (s . dsh_conf1))
  some
  ((pPartLdrID . (s . Carousel_PartitionLeader_currentTxn)).elems) and
  no
  (pPartLdrID . (s . Carousel_PartitionLeader_response)) and
  !
  (((((pPartLdrID .
         (s . Carousel_PartitionLeader_currentTxn)).firstElem).key).Value)
     in
     ((((pPartLdrID .
           (s . Carousel_PartitionLeader_pendingTxn)).elems).key).Value))
  ! (Carousel in (s . dsh_sc_used0))
  !
((pPartLdrID -> Carousel_PartitionLeader) in
   (s . dsh_sc_used1))
}


pred Carousel_PartitionLeader_Waiting_PrepareCommit_post [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pPartLdrID -> Carousel_PartitionLeader_Commit)) +
     (pPartLdrID -> Carousel_PartitionLeader_Commit))
  ((pPartLdrID . (s . Carousel_PartitionLeader_currentTxn)).firstElem).((pPartLdrID
                                                                         .
                                                                         (s
                                                                            .
                                                                            Carousel_PartitionLeader_pendingTxn)).add) and
  (pPartLdrID . (s . Carousel_PartitionLeader_currentTxn)).removeFirst
  ((pPartLdrID -> Carousel_PartitionLeader) .
   (none . (sn . (s . _testIfNextStable))))=>
    ((sn . dsh_stable) = boolean/True and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })

}

pred Carousel_PartitionLeader_Waiting_PrepareCommit_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pPartLdrID -> Carousel_PartitionLeader_Waiting) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (Carousel in dsh_scp0) and
    !
    ((pPartLdrID -> Carousel_PartitionLeader) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred Carousel_PartitionLeader_Waiting_PrepareCommit [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID] {
  pPartLdrID .
  (s . Carousel_PartitionLeader_Waiting_PrepareCommit_pre)
  pPartLdrID .
  (sn .
     (s .
        Carousel_PartitionLeader_Waiting_PrepareCommit_post))
}

pred Carousel_Coordinator_WaitForResponse_StartCommit_pre [s: one DshSnapshot, pCoordinatorID: one CoordinatorID] {
  some
((pCoordinatorID -> Carousel_Coordinator_WaitForResponse) &
   (s . dsh_conf1))
  (#
  (pCoordinatorID .
     (s . Carousel_Coordinator_coord_responses))) =
  (# PartLdrID) and
  !
  (Abort in
     (PartLdrID.(pCoordinatorID .
                   (s . Carousel_Coordinator_coord_responses))))
  ! (Carousel in (s . dsh_sc_used0))
  !
((pCoordinatorID -> Carousel_Coordinator) in
   (s . dsh_sc_used1))
}


pred Carousel_Coordinator_WaitForResponse_StartCommit_post [s: one DshSnapshot, sn: one DshSnapshot, pCoordinatorID: one CoordinatorID] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pCoordinatorID ->
         Carousel_Coordinator_WaitForResponse)) +
     (pCoordinatorID -> Carousel_Coordinator_WaitForResponse))
  ((pCoordinatorID . (s . Carousel_Coordinator_client)) .
   (sn . Carousel_Client_response)) = Commit and
  (all others: ClientID -
                 (pCoordinatorID .
                    (s . Carousel_Coordinator_client)) | (others
                                                            .
                                                            (sn
                                                               .
                                                               Carousel_Client_response))
                                                           =
                                                           (others
                                                              .
                                                              (s
                                                                 .
                                                                 Carousel_Client_response))) and
  (all leader: PartLdrID | (leader .
                              (sn .
                                 Carousel_PartitionLeader_response))
                             =
                             ((pCoordinatorID .
                                 (s .
                                    Carousel_Coordinator_currentTxn))
                                -> Commit)) and
  no
  (pCoordinatorID . (sn . Carousel_Coordinator_info)) and
  no
  (pCoordinatorID . (sn . Carousel_Coordinator_currentTxn)) and
  no
  (pCoordinatorID . (sn . Carousel_Coordinator_client)) and
  no
  (pCoordinatorID .
     (sn . Carousel_Coordinator_coord_responses))
  ((pCoordinatorID -> Carousel_Coordinator) .
   (none . (sn . (s . _testIfNextStable))))=>
    ((sn . dsh_stable) = boolean/True and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })

}

pred Carousel_Coordinator_WaitForResponse_StartCommit_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pCoordinatorID: one CoordinatorID, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pCoordinatorID -> Carousel_Coordinator_WaitForResponse) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (Carousel in dsh_scp0) and
    !
    ((pCoordinatorID -> Carousel_Coordinator) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred Carousel_Coordinator_WaitForResponse_StartCommit [s: one DshSnapshot, sn: one DshSnapshot, pCoordinatorID: one CoordinatorID] {
  pCoordinatorID .
  (s . Carousel_Coordinator_WaitForResponse_StartCommit_pre)
  pCoordinatorID .
  (sn .
     (s .
        Carousel_Coordinator_WaitForResponse_StartCommit_post))
}

pred Carousel_Client_Waiting_FinalizeAbort_pre [s: one DshSnapshot, pClientID: one ClientID] {
  some
((pClientID -> Carousel_Client_Waiting) & (s . dsh_conf1))
  one
  (pClientID . (s . Carousel_Client_response)) and
  Abort in (pClientID . (s . Carousel_Client_response))
  ! (Carousel in (s . dsh_sc_used0))
  ! ((pClientID -> Carousel_Client) in (s . dsh_sc_used1))
}


pred Carousel_Client_Waiting_FinalizeAbort_post [s: one DshSnapshot, sn: one DshSnapshot, pClientID: one ClientID] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) - (pClientID -> Carousel_Client_Reading))
     + (pClientID -> Carousel_Client_Reading))
  (pClientID . (sn . Carousel_Client_txn)) = none and
  no
  (pClientID . (sn . Carousel_Client_response))
  ((pClientID -> Carousel_Client) .
   (none . (sn . (s . _testIfNextStable))))=>
    ((sn . dsh_stable) = boolean/True and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })

}

pred Carousel_Client_Waiting_FinalizeAbort_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pClientID: one ClientID, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pClientID -> Carousel_Client_Waiting) & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (Carousel in dsh_scp0) and
    !
    ((pClientID -> Carousel_Client) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred Carousel_Client_Waiting_FinalizeAbort [s: one DshSnapshot, sn: one DshSnapshot, pClientID: one ClientID] {
  pClientID . (s . Carousel_Client_Waiting_FinalizeAbort_pre)
  pClientID .
  (sn . (s . Carousel_Client_Waiting_FinalizeAbort_post))
}

pred Carousel_PartitionLeader_Waiting_FinalizeCommit_pre [s: one DshSnapshot, pPartLdrID: one PartLdrID] {
  some
((pPartLdrID -> Carousel_PartitionLeader_Waiting) &
   (s . dsh_conf1))
  Commit in
  (Transaction.(pPartLdrID .
                  (s . Carousel_PartitionLeader_response)))
  ! (Carousel in (s . dsh_sc_used0))
  !
((pPartLdrID -> Carousel_PartitionLeader) in
   (s . dsh_sc_used1))
}


pred Carousel_PartitionLeader_Waiting_FinalizeCommit_post [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pPartLdrID -> Carousel_PartitionLeader_Waiting)) +
     (pPartLdrID -> Carousel_PartitionLeader_Waiting))
  no
  (pPartLdrID . (sn . Carousel_PartitionLeader_response)) and
  (pPartLdrID . (s . Carousel_PartitionLeader_pendingTxn)).removeFirst and
  (pPartLdrID . (sn . Carousel_PartitionLeader_data)) =
    ((pPartLdrID . (s . Carousel_PartitionLeader_data)) ++
       (((pPartLdrID .
            (s . Carousel_PartitionLeader_response)).Response).key))
  ((pPartLdrID -> Carousel_PartitionLeader) .
   (none . (sn . (s . _testIfNextStable))))=>
    ((sn . dsh_stable) = boolean/True and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })

}

pred Carousel_PartitionLeader_Waiting_FinalizeCommit_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pPartLdrID -> Carousel_PartitionLeader_Waiting) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (Carousel in dsh_scp0) and
    !
    ((pPartLdrID -> Carousel_PartitionLeader) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred Carousel_PartitionLeader_Waiting_FinalizeCommit [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID] {
  pPartLdrID .
  (s . Carousel_PartitionLeader_Waiting_FinalizeCommit_pre)
  pPartLdrID .
  (sn .
     (s .
        Carousel_PartitionLeader_Waiting_FinalizeCommit_post))
}

pred Carousel_PartitionLeader_Waiting_PrepareAbort_pre [s: one DshSnapshot, pPartLdrID: one PartLdrID] {
  some
((pPartLdrID -> Carousel_PartitionLeader_Waiting) &
   (s . dsh_conf1))
  some
  ((pPartLdrID . (s . Carousel_PartitionLeader_currentTxn)).elems) and
  ((((pPartLdrID . (s . Carousel_PartitionLeader_currentTxn)).firstElem).key).Value)
    in
    ((((pPartLdrID .
          (s . Carousel_PartitionLeader_pendingTxn)).elems).key).Value)
  ! (Carousel in (s . dsh_sc_used0))
  !
((pPartLdrID -> Carousel_PartitionLeader) in
   (s . dsh_sc_used1))
}


pred Carousel_PartitionLeader_Waiting_PrepareAbort_post [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pPartLdrID -> Carousel_PartitionLeader_Abort)) +
     (pPartLdrID -> Carousel_PartitionLeader_Abort))
  ((pPartLdrID -> Carousel_PartitionLeader) .
   (none . (sn . (s . _testIfNextStable))))=>
    ((sn . dsh_stable) = boolean/True and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })

}

pred Carousel_PartitionLeader_Waiting_PrepareAbort_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pPartLdrID -> Carousel_PartitionLeader_Waiting) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (Carousel in dsh_scp0) and
    !
    ((pPartLdrID -> Carousel_PartitionLeader) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred Carousel_PartitionLeader_Waiting_PrepareAbort [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID] {
  pPartLdrID .
  (s . Carousel_PartitionLeader_Waiting_PrepareAbort_pre)
  pPartLdrID .
  (sn .
     (s . Carousel_PartitionLeader_Waiting_PrepareAbort_post))
}

pred Carousel_Coordinator_Replicate_Replicating_pre [s: one DshSnapshot, pCoordinatorID: one CoordinatorID] {
  some
((pCoordinatorID -> Carousel_Coordinator_Replicate) &
   (s . dsh_conf1))
  one (pCoordinatorID . (s . Carousel_Coordinator_currentTxn))
  ! (Carousel in (s . dsh_sc_used0))
  !
((pCoordinatorID -> Carousel_Coordinator) in
   (s . dsh_sc_used1))
}


pred Carousel_Coordinator_Replicate_Replicating_post [s: one DshSnapshot, sn: one DshSnapshot, pCoordinatorID: one CoordinatorID] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pCoordinatorID ->
         Carousel_Coordinator_WaitForResponse)) +
     (pCoordinatorID -> Carousel_Coordinator_WaitForResponse))
  (pCoordinatorID . (sn . Carousel_Coordinator_info)) =
  ((pCoordinatorID . (s . Carousel_Coordinator_currentTxn)).key)
  ((pCoordinatorID -> Carousel_Coordinator) .
   (none . (sn . (s . _testIfNextStable))))=>
    ((sn . dsh_stable) = boolean/True and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })

}

pred Carousel_Coordinator_Replicate_Replicating_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pCoordinatorID: one CoordinatorID, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pCoordinatorID -> Carousel_Coordinator_Replicate) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (Carousel in dsh_scp0) and
    !
    ((pCoordinatorID -> Carousel_Coordinator) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred Carousel_Coordinator_Replicate_Replicating [s: one DshSnapshot, sn: one DshSnapshot, pCoordinatorID: one CoordinatorID] {
  pCoordinatorID .
  (s . Carousel_Coordinator_Replicate_Replicating_pre)
  pCoordinatorID .
  (sn .
     (s . Carousel_Coordinator_Replicate_Replicating_post))
}

pred Carousel_PartitionLeader_Commit_CommitTransaction_pre [s: one DshSnapshot, pPartLdrID: one PartLdrID] {
  some
((pPartLdrID -> Carousel_PartitionLeader_Commit) &
   (s . dsh_conf1))
  ! (Carousel in (s . dsh_sc_used0))
  !
((pPartLdrID -> Carousel_PartitionLeader) in
   (s . dsh_sc_used1))
}


pred Carousel_PartitionLeader_Commit_CommitTransaction_post [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pPartLdrID -> Carousel_PartitionLeader_Waiting)) +
     (pPartLdrID -> Carousel_PartitionLeader_Waiting))
  ((((pPartLdrID . (s . Carousel_PartitionLeader_pendingTxn)).firstElem).coordinator)
   . (sn . Carousel_Coordinator_coord_responses)) =
  (((((pPartLdrID .
         (s . Carousel_PartitionLeader_pendingTxn)).firstElem).coordinator)
      . (s . Carousel_Coordinator_coord_responses)) +
     (pPartLdrID -> Commit)) and
  (all others: CoordinatorID -
                 (((pPartLdrID .
                      (s .
                         Carousel_PartitionLeader_pendingTxn)).firstElem).coordinator) | (others
                                                                                            .
                                                                                            (sn
                                                                                               .
                                                                                               Carousel_Coordinator_coord_responses))
                                                                                           =
                                                                                           (others
                                                                                              .
                                                                                              (s
                                                                                                 .
                                                                                                 Carousel_Coordinator_coord_responses)))
  ((pPartLdrID -> Carousel_PartitionLeader) .
   (none . (sn . (s . _testIfNextStable))))=>
    ((sn . dsh_stable) = boolean/True and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })

}

pred Carousel_PartitionLeader_Commit_CommitTransaction_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pPartLdrID -> Carousel_PartitionLeader_Commit) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (Carousel in dsh_scp0) and
    !
    ((pPartLdrID -> Carousel_PartitionLeader) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred Carousel_PartitionLeader_Commit_CommitTransaction [s: one DshSnapshot, sn: one DshSnapshot, pPartLdrID: one PartLdrID] {
  pPartLdrID .
  (s . Carousel_PartitionLeader_Commit_CommitTransaction_pre)
  pPartLdrID .
  (sn .
     (s .
        Carousel_PartitionLeader_Commit_CommitTransaction_post))
}

pred _testIfNextStable [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            Carousel_Client_Waiting_FinalizeCommit_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            Carousel_PartitionLeader_Abort_AbortTransaction_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            Carousel_Client_Reading_ReadAndPrepare_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            Carousel_Coordinator_WaitForResponse_StartAbort_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            Carousel_PartitionLeader_Waiting_PrepareCommit_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            Carousel_Coordinator_WaitForResponse_StartCommit_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            Carousel_Client_Waiting_FinalizeAbort_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            Carousel_PartitionLeader_Waiting_FinalizeCommit_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            Carousel_PartitionLeader_Waiting_PrepareAbort_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            Carousel_Coordinator_Replicate_Replicating_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            Carousel_PartitionLeader_Commit_CommitTransaction_enabledAfterStep))))
}

pred dsh_small_step [s: one DshSnapshot, sn: one DshSnapshot] {
  (some pPartLdrID: one
  PartLdrID,pClientID: one
  ClientID,pCoordinatorID: one
  CoordinatorID | { pClientID .
                      (sn .
                         (s .
                            Carousel_Client_Waiting_FinalizeCommit)) or
                      pPartLdrID .
                        (sn .
                           (s .
                              Carousel_PartitionLeader_Abort_AbortTransaction)) or
                      pClientID .
                        (sn .
                           (s .
                              Carousel_Client_Reading_ReadAndPrepare)) or
                      pCoordinatorID .
                        (sn .
                           (s .
                              Carousel_Coordinator_WaitForResponse_StartAbort)) or
                      pPartLdrID .
                        (sn .
                           (s .
                              Carousel_PartitionLeader_Waiting_PrepareCommit)) or
                      pCoordinatorID .
                        (sn .
                           (s .
                              Carousel_Coordinator_WaitForResponse_StartCommit)) or
                      pClientID .
                        (sn .
                           (s .
                              Carousel_Client_Waiting_FinalizeAbort)) or
                      pPartLdrID .
                        (sn .
                           (s .
                              Carousel_PartitionLeader_Waiting_FinalizeCommit)) or
                      pPartLdrID .
                        (sn .
                           (s .
                              Carousel_PartitionLeader_Waiting_PrepareAbort)) or
                      pCoordinatorID .
                        (sn .
                           (s .
                              Carousel_Coordinator_Replicate_Replicating)) or
                      pPartLdrID .
                        (sn .
                           (s .
                              Carousel_PartitionLeader_Commit_CommitTransaction)) })
}

fact dsh_traces_fact {  DshSnapshot/first . dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s . DshSnapshot/next)
                                       .
                                       (s . dsh_small_step))
}

