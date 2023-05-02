open util/boolean
open util/ordering[Snapshot] as Snapshot
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

assert bothFinalize {
    always (some c: one ClientID, p: one PartLdrID | Carousel_PartitionLeader_Commit in (p.(Identifiers <: conf1)) => (
        eventually always (Carousel_Client_Waiting_FinalizeCommit in c. (Identifiers <: taken1))))
}


assert bothAbort {
    always  (some c: one ClientID,p: one PartLdrID | Carousel_PartitionLeader_Abort in p. ((Identifiers <: conf1)) => eventually always {
       (Carousel_Client_Waiting_FinalizeAbort in c. ((Identifiers <: taken1)))})
}

assert commitUpdatesData {
    always (some c: one CoordinatorID | Carousel_Coordinator_WaitForResponse_StartCommit in c.(Identifiers <: taken1) => eventually always
        (all p: PartLdrID | c.(Carousel_Coordinator_info) in p.(Carousel_PartitionLeader_data)))
}

assert cannotBothCommitAndAbort {
    always (one disj p0, p1: PartLdrID | (Carousel_PartitionLeader_Waiting_FinalizeCommit in (p0.(Identifiers <: taken1))) 
	=> always (Carousel_PartitionLeader_Abort !in p1.(Identifiers <: conf1)))
}

// remember to have electrum option set

check bothFinalize for 23 steps, exactly 3 Key, exactly 2 Value, exactly 4 Transaction, exactly 2 ClientID, exactly 2 CoordinatorID, exactly 2 PartLdrID, 3 currentTxn, 3 pendingTxn
check bothFinalize for 30 steps, exactly 3 Key, exactly 2 Value, exactly 4 Transaction, exactly 2 ClientID, exactly 2 CoordinatorID, exactly 3 PartLdrID, 3 currentTxn, 3 pendingTxn
check bothAbort for 23 steps, exactly 3 Key, exactly 2 Value, exactly 4 Transaction, exactly 2 ClientID, exactly 2 CoordinatorID, exactly 2 PartLdrID, 3 currentTxn, 3 pendingTxn
check bothAbort for 30 steps, exactly 3 Key, exactly 2 Value, exactly 4 Transaction, exactly 2 ClientID, exactly 2 CoordinatorID, exactly 3 PartLdrID, 3 currentTxn, 3 pendingTxn
check cannotBothCommitAndAbort for 23 steps, exactly 3 Key, exactly 2 Value, exactly 4 Transaction, exactly 2 ClientID, exactly 2 CoordinatorID, exactly 2 PartLdrID, 3 currentTxn, 3 pendingTxn
check cannotBothCommitAndAbort for 30 steps, exactly 3 Key, exactly 2 Value, exactly 4 Transaction, exactly 2 ClientID, exactly 2 CoordinatorID, exactly 3 PartLdrID, 3 currentTxn, 3 pendingTxn
check commitUpdatesData for 23 steps, exactly 3 Key, exactly 2 Value, exactly 4 Transaction, exactly 2 ClientID, exactly 2 CoordinatorID, exactly 2 PartLdrID, 3 currentTxn, 3 pendingTxn
check commitUpdatesData for 30 steps, exactly 3 Key, exactly 2 Value, exactly 4 Transaction, exactly 2 ClientID, exactly 2 CoordinatorID, exactly 3 PartLdrID, 3 currentTxn, 3 pendingTxn

abstract sig StateLabel {}
sig Carousel extends StateLabel {} 
one sig Carousel_Client extends Carousel {} 
one sig Carousel_Client_Reading extends Carousel_Client {} 
one sig Carousel_Client_Waiting extends Carousel_Client {} 
one sig Carousel_Coordinator extends Carousel {} 
one sig Carousel_Coordinator_Replicate extends Carousel_Coordinator {} 
one sig Carousel_Coordinator_WaitForResponse extends Carousel_Coordinator {} 
one sig Carousel_PartitionLeader extends Carousel {} 
one sig Carousel_PartitionLeader_Waiting extends Carousel_PartitionLeader {} 
one sig Carousel_PartitionLeader_Commit extends Carousel_PartitionLeader {} 
one sig Carousel_PartitionLeader_Abort extends Carousel_PartitionLeader {} 

abstract sig Identifiers {}
sig PartLdrID extends Identifiers {} 
sig ClientID extends Identifiers {} 
sig CoordinatorID extends Identifiers {} 

sig Snapshot {
  scopesUsed0 : set StateLabel,
  conf0 : set StateLabel,
  scopesUsed1 : Identifiers -> Identifiers -> StateLabel,
  conf1 : Identifiers -> Identifiers -> StateLabel,
  stable : one boolean/Bool
}

pred Carousel_Client_Waiting_FinalizeCommit_pre[s : one Snapshot, pClientID : one ClientID] {
  { pClientID -> Carousel/Client/Waiting } in s. (conf1)
  ! {Carousel in scopesUsed0}
  ! {{ pClientID -> Carousel/Client } in scopesUsed1}
}


pred Carousel_Client_Waiting_FinalizeCommit_post[s : one Snapshot, sNext : one Snapshot, pClientID : one ClientID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pClientID -> Carousel/Client/Reading } - { pClientID -> Carousel/Client/Waiting } } + { pClientID -> Carousel/Client/Reading } }
  (pClientID -> Carousel/Client. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred Carousel_Client_Waiting_FinalizeCommit_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pClientID -> Carousel/Client/Waiting } in sNext. (conf1)
}

pred Carousel_Client_Waiting_FinalizeCommit[s : one Snapshot, sNext : one Snapshot, pClientID : one ClientID] {
  pClientID. (s. (Carousel_Client_Waiting_FinalizeCommit_pre))
  pClientID. (sNext. (s. (Carousel_Client_Waiting_FinalizeCommit_post)))
}

pred Carousel_PartitionLeader_Abort_AbortTransaction_pre[s : one Snapshot, pPartLdrID : one PartLdrID] {
  { pPartLdrID -> Carousel/PartitionLeader/Abort } in s. (conf1)
  ! {Carousel in scopesUsed0}
  ! {{ pPartLdrID -> Carousel/PartitionLeader } in scopesUsed1}
}


pred Carousel_PartitionLeader_Abort_AbortTransaction_post[s : one Snapshot, sNext : one Snapshot, pPartLdrID : one PartLdrID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPartLdrID -> Carousel/PartitionLeader/Waiting } - { pPartLdrID -> Carousel/PartitionLeader/Commit } - { pPartLdrID -> Carousel/PartitionLeader/Abort } } + { pPartLdrID -> Carousel/PartitionLeader/Waiting } }
  (pPartLdrID -> Carousel/PartitionLeader. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred Carousel_PartitionLeader_Abort_AbortTransaction_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPartLdrID -> Carousel/PartitionLeader/Abort } in sNext. (conf1)
}

pred Carousel_PartitionLeader_Abort_AbortTransaction[s : one Snapshot, sNext : one Snapshot, pPartLdrID : one PartLdrID] {
  pPartLdrID. (s. (Carousel_PartitionLeader_Abort_AbortTransaction_pre))
  pPartLdrID. (sNext. (s. (Carousel_PartitionLeader_Abort_AbortTransaction_post)))
}

pred Carousel_Client_Reading_ReadAndPrepare_pre[s : one Snapshot, pClientID : one ClientID] {
  { pClientID -> Carousel/Client/Reading } in s. (conf1)
  ! {Carousel in scopesUsed0}
  ! {{ pClientID -> Carousel/Client } in scopesUsed1}
}


pred Carousel_Client_Reading_ReadAndPrepare_post[s : one Snapshot, sNext : one Snapshot, pClientID : one ClientID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pClientID -> Carousel/Client/Reading } - { pClientID -> Carousel/Client/Waiting } } + { pClientID -> Carousel/Client/Waiting } }
  (pClientID -> Carousel/Client. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred Carousel_Client_Reading_ReadAndPrepare_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pClientID -> Carousel/Client/Reading } in sNext. (conf1)
}

pred Carousel_Client_Reading_ReadAndPrepare[s : one Snapshot, sNext : one Snapshot, pClientID : one ClientID] {
  pClientID. (s. (Carousel_Client_Reading_ReadAndPrepare_pre))
  pClientID. (sNext. (s. (Carousel_Client_Reading_ReadAndPrepare_post)))
}

pred Carousel_Coordinator_WaitForResponse_StartAbort_pre[s : one Snapshot, pCoordinatorID : one CoordinatorID] {
  { pCoordinatorID -> Carousel/Coordinator/WaitForResponse } in s. (conf1)
  ! {Carousel in scopesUsed0}
  ! {{ pCoordinatorID -> Carousel/Coordinator } in scopesUsed1}
}


pred Carousel_Coordinator_WaitForResponse_StartAbort_post[s : one Snapshot, sNext : one Snapshot, pCoordinatorID : one CoordinatorID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pCoordinatorID -> Carousel/Coordinator/WaitForResponse } } + { pCoordinatorID -> Carousel/Coordinator/WaitForResponse } }
  (pCoordinatorID -> Carousel/Coordinator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred Carousel_Coordinator_WaitForResponse_StartAbort_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pCoordinatorID -> Carousel/Coordinator/WaitForResponse } in sNext. (conf1)
}

pred Carousel_Coordinator_WaitForResponse_StartAbort[s : one Snapshot, sNext : one Snapshot, pCoordinatorID : one CoordinatorID] {
  pCoordinatorID. (s. (Carousel_Coordinator_WaitForResponse_StartAbort_pre))
  pCoordinatorID. (sNext. (s. (Carousel_Coordinator_WaitForResponse_StartAbort_post)))
}

pred Carousel_PartitionLeader_Waiting_PrepareCommit_pre[s : one Snapshot, pPartLdrID : one PartLdrID] {
  { pPartLdrID -> Carousel/PartitionLeader/Waiting } in s. (conf1)
  ! {Carousel in scopesUsed0}
  ! {{ pPartLdrID -> Carousel/PartitionLeader } in scopesUsed1}
}


pred Carousel_PartitionLeader_Waiting_PrepareCommit_post[s : one Snapshot, sNext : one Snapshot, pPartLdrID : one PartLdrID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPartLdrID -> Carousel/PartitionLeader/Waiting } - { pPartLdrID -> Carousel/PartitionLeader/Commit } - { pPartLdrID -> Carousel/PartitionLeader/Abort } } + { pPartLdrID -> Carousel/PartitionLeader/Commit } }
  (pPartLdrID -> Carousel/PartitionLeader. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred Carousel_PartitionLeader_Waiting_PrepareCommit_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPartLdrID -> Carousel/PartitionLeader/Waiting } in sNext. (conf1)
}

pred Carousel_PartitionLeader_Waiting_PrepareCommit[s : one Snapshot, sNext : one Snapshot, pPartLdrID : one PartLdrID] {
  pPartLdrID. (s. (Carousel_PartitionLeader_Waiting_PrepareCommit_pre))
  pPartLdrID. (sNext. (s. (Carousel_PartitionLeader_Waiting_PrepareCommit_post)))
}

pred Carousel_Coordinator_WaitForResponse_StartCommit_pre[s : one Snapshot, pCoordinatorID : one CoordinatorID] {
  { pCoordinatorID -> Carousel/Coordinator/WaitForResponse } in s. (conf1)
  ! {Carousel in scopesUsed0}
  ! {{ pCoordinatorID -> Carousel/Coordinator } in scopesUsed1}
}


pred Carousel_Coordinator_WaitForResponse_StartCommit_post[s : one Snapshot, sNext : one Snapshot, pCoordinatorID : one CoordinatorID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pCoordinatorID -> Carousel/Coordinator/WaitForResponse } } + { pCoordinatorID -> Carousel/Coordinator/WaitForResponse } }
  (pCoordinatorID -> Carousel/Coordinator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred Carousel_Coordinator_WaitForResponse_StartCommit_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pCoordinatorID -> Carousel/Coordinator/WaitForResponse } in sNext. (conf1)
}

pred Carousel_Coordinator_WaitForResponse_StartCommit[s : one Snapshot, sNext : one Snapshot, pCoordinatorID : one CoordinatorID] {
  pCoordinatorID. (s. (Carousel_Coordinator_WaitForResponse_StartCommit_pre))
  pCoordinatorID. (sNext. (s. (Carousel_Coordinator_WaitForResponse_StartCommit_post)))
}

pred Carousel_Client_Waiting_FinalizeAbort_pre[s : one Snapshot, pClientID : one ClientID] {
  { pClientID -> Carousel/Client/Waiting } in s. (conf1)
  ! {Carousel in scopesUsed0}
  ! {{ pClientID -> Carousel/Client } in scopesUsed1}
}


pred Carousel_Client_Waiting_FinalizeAbort_post[s : one Snapshot, sNext : one Snapshot, pClientID : one ClientID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pClientID -> Carousel/Client/Reading } - { pClientID -> Carousel/Client/Waiting } } + { pClientID -> Carousel/Client/Reading } }
  (pClientID -> Carousel/Client. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred Carousel_Client_Waiting_FinalizeAbort_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pClientID -> Carousel/Client/Waiting } in sNext. (conf1)
}

pred Carousel_Client_Waiting_FinalizeAbort[s : one Snapshot, sNext : one Snapshot, pClientID : one ClientID] {
  pClientID. (s. (Carousel_Client_Waiting_FinalizeAbort_pre))
  pClientID. (sNext. (s. (Carousel_Client_Waiting_FinalizeAbort_post)))
}

pred Carousel_PartitionLeader_Waiting_FinalizeCommit_pre[s : one Snapshot, pPartLdrID : one PartLdrID] {
  { pPartLdrID -> Carousel/PartitionLeader/Waiting } in s. (conf1)
  ! {Carousel in scopesUsed0}
  ! {{ pPartLdrID -> Carousel/PartitionLeader } in scopesUsed1}
}


pred Carousel_PartitionLeader_Waiting_FinalizeCommit_post[s : one Snapshot, sNext : one Snapshot, pPartLdrID : one PartLdrID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPartLdrID -> Carousel/PartitionLeader/Waiting } } + { pPartLdrID -> Carousel/PartitionLeader/Waiting } }
  (pPartLdrID -> Carousel/PartitionLeader. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred Carousel_PartitionLeader_Waiting_FinalizeCommit_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPartLdrID -> Carousel/PartitionLeader/Waiting } in sNext. (conf1)
}

pred Carousel_PartitionLeader_Waiting_FinalizeCommit[s : one Snapshot, sNext : one Snapshot, pPartLdrID : one PartLdrID] {
  pPartLdrID. (s. (Carousel_PartitionLeader_Waiting_FinalizeCommit_pre))
  pPartLdrID. (sNext. (s. (Carousel_PartitionLeader_Waiting_FinalizeCommit_post)))
}

pred Carousel_PartitionLeader_Waiting_PrepareAbort_pre[s : one Snapshot, pPartLdrID : one PartLdrID] {
  { pPartLdrID -> Carousel/PartitionLeader/Waiting } in s. (conf1)
  ! {Carousel in scopesUsed0}
  ! {{ pPartLdrID -> Carousel/PartitionLeader } in scopesUsed1}
}


pred Carousel_PartitionLeader_Waiting_PrepareAbort_post[s : one Snapshot, sNext : one Snapshot, pPartLdrID : one PartLdrID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPartLdrID -> Carousel/PartitionLeader/Waiting } - { pPartLdrID -> Carousel/PartitionLeader/Commit } - { pPartLdrID -> Carousel/PartitionLeader/Abort } } + { pPartLdrID -> Carousel/PartitionLeader/Abort } }
  (pPartLdrID -> Carousel/PartitionLeader. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred Carousel_PartitionLeader_Waiting_PrepareAbort_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPartLdrID -> Carousel/PartitionLeader/Waiting } in sNext. (conf1)
}

pred Carousel_PartitionLeader_Waiting_PrepareAbort[s : one Snapshot, sNext : one Snapshot, pPartLdrID : one PartLdrID] {
  pPartLdrID. (s. (Carousel_PartitionLeader_Waiting_PrepareAbort_pre))
  pPartLdrID. (sNext. (s. (Carousel_PartitionLeader_Waiting_PrepareAbort_post)))
}

pred Carousel_Coordinator_Replicate_Replicating_pre[s : one Snapshot, pCoordinatorID : one CoordinatorID] {
  { pCoordinatorID -> Carousel/Coordinator/Replicate } in s. (conf1)
  ! {Carousel in scopesUsed0}
  ! {{ pCoordinatorID -> Carousel/Coordinator } in scopesUsed1}
}


pred Carousel_Coordinator_Replicate_Replicating_post[s : one Snapshot, sNext : one Snapshot, pCoordinatorID : one CoordinatorID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pCoordinatorID -> Carousel/Coordinator/Replicate } - { pCoordinatorID -> Carousel/Coordinator/WaitForResponse } } + { pCoordinatorID -> Carousel/Coordinator/WaitForResponse } }
  (pCoordinatorID -> Carousel/Coordinator. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred Carousel_Coordinator_Replicate_Replicating_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pCoordinatorID -> Carousel/Coordinator/Replicate } in sNext. (conf1)
}

pred Carousel_Coordinator_Replicate_Replicating[s : one Snapshot, sNext : one Snapshot, pCoordinatorID : one CoordinatorID] {
  pCoordinatorID. (s. (Carousel_Coordinator_Replicate_Replicating_pre))
  pCoordinatorID. (sNext. (s. (Carousel_Coordinator_Replicate_Replicating_post)))
}

pred Carousel_PartitionLeader_Commit_CommitTransaction_pre[s : one Snapshot, pPartLdrID : one PartLdrID] {
  { pPartLdrID -> Carousel/PartitionLeader/Commit } in s. (conf1)
  ! {Carousel in scopesUsed0}
  ! {{ pPartLdrID -> Carousel/PartitionLeader } in scopesUsed1}
}


pred Carousel_PartitionLeader_Commit_CommitTransaction_post[s : one Snapshot, sNext : one Snapshot, pPartLdrID : one PartLdrID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pPartLdrID -> Carousel/PartitionLeader/Waiting } - { pPartLdrID -> Carousel/PartitionLeader/Commit } - { pPartLdrID -> Carousel/PartitionLeader/Abort } } + { pPartLdrID -> Carousel/PartitionLeader/Waiting } }
  (pPartLdrID -> Carousel/PartitionLeader. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred Carousel_PartitionLeader_Commit_CommitTransaction_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pPartLdrID -> Carousel/PartitionLeader/Commit } in sNext. (conf1)
}

pred Carousel_PartitionLeader_Commit_CommitTransaction[s : one Snapshot, sNext : one Snapshot, pPartLdrID : one PartLdrID] {
  pPartLdrID. (s. (Carousel_PartitionLeader_Commit_CommitTransaction_pre))
  pPartLdrID. (sNext. (s. (Carousel_PartitionLeader_Commit_CommitTransaction_post)))
}

pred testIfNextStable[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (Carousel_Client_Waiting_FinalizeCommit_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (Carousel_PartitionLeader_Abort_AbortTransaction_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (Carousel_Client_Reading_ReadAndPrepare_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (Carousel_Coordinator_WaitForResponse_StartAbort_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (Carousel_PartitionLeader_Waiting_PrepareCommit_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (Carousel_Coordinator_WaitForResponse_StartCommit_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (Carousel_Client_Waiting_FinalizeAbort_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (Carousel_PartitionLeader_Waiting_FinalizeCommit_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (Carousel_PartitionLeader_Waiting_PrepareAbort_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (Carousel_Coordinator_Replicate_Replicating_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (Carousel_PartitionLeader_Commit_CommitTransaction_enabledAfterStep))))}
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  (some pPartLdrID: one PartLdrID,pClientID: one ClientID,pCoordinatorID: one CoordinatorID | { pClientID. (sNext. (s. (Carousel_Client_Waiting_FinalizeCommit))) or
    pPartLdrID. (sNext. (s. (Carousel_PartitionLeader_Abort_AbortTransaction))) or
    pClientID. (sNext. (s. (Carousel_Client_Reading_ReadAndPrepare))) or
    pCoordinatorID. (sNext. (s. (Carousel_Coordinator_WaitForResponse_StartAbort))) or
    pPartLdrID. (sNext. (s. (Carousel_PartitionLeader_Waiting_PrepareCommit))) or
    pCoordinatorID. (sNext. (s. (Carousel_Coordinator_WaitForResponse_StartCommit))) or
    pClientID. (sNext. (s. (Carousel_Client_Waiting_FinalizeAbort))) or
    pPartLdrID. (sNext. (s. (Carousel_PartitionLeader_Waiting_FinalizeCommit))) or
    pPartLdrID. (sNext. (s. (Carousel_PartitionLeader_Waiting_PrepareAbort))) or
    pCoordinatorID. (sNext. (s. (Carousel_Coordinator_Replicate_Replicating))) or
    pPartLdrID. (sNext. (s. (Carousel_PartitionLeader_Commit_CommitTransaction))) })
}

