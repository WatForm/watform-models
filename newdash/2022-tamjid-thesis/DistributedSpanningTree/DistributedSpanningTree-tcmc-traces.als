open util/ordering[Level] as nodeLevel

open util/boolean
open util/ordering[Snapshot] as Snapshot

sig Level {}

assert ctl_noCycles  {
	ctl_mc[ag[{ s: Snapshot | all n: Node -  s.DistrubedTreeSpanning_root | n !in n.(^(~(s.DistrubedTreeSpanning_N_parent)))}]]
}

assert ctl_topologyOverAllNodes {
	ctl_mc[eg[{ s: Snapshot | all n: Node | some n.(s.DistrubedTreeSpanning_N_level)}]]
}

check ctl_noCycles for 9 Snapshot, exactly 4 Node, exactly 4 Level, 1 PathNode
check ctl_noCycles for 11 Snapshot, exactly 5 Node, exactly 5 Level, 1 PathNode
check ctl_noCycles for 13 Snapshot, exactly 6 Node, exactly 6 Level, 1 PathNode
check ctl_topologyOverAllNodes for 9 Snapshot, exactly 4 Node, exactly 4 Level, 1 PathNode
check ctl_topologyOverAllNodes for 11 Snapshot, exactly 5 Node, exactly 5 Level, 1 PathNode
check ctl_topologyOverAllNodes for 13 Snapshot, exactly 6 Node, exactly 6 Level, 1 PathNode
abstract sig StateLabel {}
sig DistributedTreeSpanning extends StateLabel {} 
one sig DistributedTreeSpanning_N extends DistributedTreeSpanning {} 
one sig DistributedTreeSpanning_N_Unassigned extends DistributedTreeSpanning_N {} 
one sig DistributedTreeSpanning_N_Assigned extends DistributedTreeSpanning_N {} 

abstract sig Identifiers {}
sig Node extends Identifiers {} 

sig Snapshot {
  scopesUsed0 : set StateLabel,
  conf0 : set StateLabel,
  scopesUsed1 : Identifiers -> Identifiers -> StateLabel,
  conf1 : Identifiers -> Identifiers -> StateLabel,
  stable : one boolean/Bool
}

pred DistributedTreeSpanning_N_Assigned_sendMessage_pre[s : one Snapshot, pNode : one Node] {
  { pNode -> DistributedTreeSpanning/N/Assigned } in s. (conf1)
  ! {DistributedTreeSpanning in scopesUsed0}
  ! {{ pNode -> DistributedTreeSpanning/N } in scopesUsed1}
}


pred DistributedTreeSpanning_N_Assigned_sendMessage_post[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pNode -> DistributedTreeSpanning/N/Assigned } } + { pNode -> DistributedTreeSpanning/N/Assigned } }
  (pNode -> DistributedTreeSpanning/N. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred DistributedTreeSpanning_N_Assigned_sendMessage_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pNode -> DistributedTreeSpanning/N/Assigned } in sNext. (conf1)
}

pred DistributedTreeSpanning_N_Assigned_sendMessage[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  pNode. (s. (DistributedTreeSpanning_N_Assigned_sendMessage_pre))
  pNode. (sNext. (s. (DistributedTreeSpanning_N_Assigned_sendMessage_post)))
}

pred DistributedTreeSpanning_N_Unassigned_RootAssign_pre[s : one Snapshot, pNode : one Node] {
  { pNode -> DistributedTreeSpanning/N/Unassigned } in s. (conf1)
  ! {DistributedTreeSpanning in scopesUsed0}
  ! {{ pNode -> DistributedTreeSpanning/N } in scopesUsed1}
}


pred DistributedTreeSpanning_N_Unassigned_RootAssign_post[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pNode -> DistributedTreeSpanning/N/Unassigned } - { pNode -> DistributedTreeSpanning/N/Assigned } } + { pNode -> DistributedTreeSpanning/N/Assigned } }
  (pNode -> DistributedTreeSpanning/N. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred DistributedTreeSpanning_N_Unassigned_RootAssign_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pNode -> DistributedTreeSpanning/N/Unassigned } in sNext. (conf1)
}

pred DistributedTreeSpanning_N_Unassigned_RootAssign[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  pNode. (s. (DistributedTreeSpanning_N_Unassigned_RootAssign_pre))
  pNode. (sNext. (s. (DistributedTreeSpanning_N_Unassigned_RootAssign_post)))
}

pred DistributedTreeSpanning_N_Unassigned_NodeAssign_pre[s : one Snapshot, pNode : one Node] {
  { pNode -> DistributedTreeSpanning/N/Unassigned } in s. (conf1)
  ! {DistributedTreeSpanning in scopesUsed0}
  ! {{ pNode -> DistributedTreeSpanning/N } in scopesUsed1}
}


pred DistributedTreeSpanning_N_Unassigned_NodeAssign_post[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pNode -> DistributedTreeSpanning/N/Unassigned } - { pNode -> DistributedTreeSpanning/N/Assigned } } + { pNode -> DistributedTreeSpanning/N/Assigned } }
  (pNode -> DistributedTreeSpanning/N. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred DistributedTreeSpanning_N_Unassigned_NodeAssign_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pNode -> DistributedTreeSpanning/N/Unassigned } in sNext. (conf1)
}

pred DistributedTreeSpanning_N_Unassigned_NodeAssign[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  pNode. (s. (DistributedTreeSpanning_N_Unassigned_NodeAssign_pre))
  pNode. (sNext. (s. (DistributedTreeSpanning_N_Unassigned_NodeAssign_post)))
}

pred testIfNextStable[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (DistributedTreeSpanning_N_Assigned_sendMessage_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (DistributedTreeSpanning_N_Unassigned_RootAssign_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (DistributedTreeSpanning_N_Unassigned_NodeAssign_enabledAfterStep))))}
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  (some pNode: one Node | { pNode. (sNext. (s. (DistributedTreeSpanning_N_Assigned_sendMessage))) or
    pNode. (sNext. (s. (DistributedTreeSpanning_N_Unassigned_RootAssign))) or
    pNode. (sNext. (s. (DistributedTreeSpanning_N_Unassigned_NodeAssign))) })
}

