open util/ordering[Level] as nodeLevel

open util/boolean
open util/ordering[Snapshot] as Snapshot

sig Level {}

assert noCycles {
	always (all n: Node -  Variables.DistrubedTreeSpanning_root | n !in n.(^(~(DistrubedTreeSpanning_N_parent))))
}

assert topologyOverAllNodes {
	eventually (all n: Node | some n.(DistrubedTreeSpanning_N_level))
}

check noCycles for 9 steps, exactly 4 Node, exactly 4 Level
check noCycles for 11 steps, exactly 5 Node, exactly 5 Level
check noCycles for 13 steps, exactly 6 Node, exactly 6 Level
check topologyOverAllNodes for 9 steps, exactly 4 Node, exactly 4 Level
check topologyOverAllNodes for 11 steps, exactly 5 Node, exactly 5 Level
check topologyOverAllNodes for 13 steps, exactly 6 Node, exactly 6 Level
abstract sig StateLabel {}
sig DistrubedTreeSpanning extends StateLabel {} 
one sig DistrubedTreeSpanning_N extends DistrubedTreeSpanning {} 
one sig DistrubedTreeSpanning_N_Unassigned extends DistrubedTreeSpanning_N {} 
one sig DistrubedTreeSpanning_N_Assigned extends DistrubedTreeSpanning_N {} 

abstract sig Identifiers {}
sig Node extends Identifiers {} 

sig Snapshot {
  scopesUsed0 : set StateLabel,
  conf0 : set StateLabel,
  scopesUsed1 : Identifiers -> Identifiers -> StateLabel,
  conf1 : Identifiers -> Identifiers -> StateLabel,
  stable : one boolean/Bool
}

pred DistrubedTreeSpanning_N_Assigned_sendMessage_pre[s : one Snapshot, pNode : one Node] {
  { pNode -> DistrubedTreeSpanning/N/Assigned } in s. (conf1)
  ! {DistrubedTreeSpanning in s. (scopesUsed0)}
  ! {{ pNode -> DistrubedTreeSpanning/N } in s. (scopesUsed1)}
}


pred DistrubedTreeSpanning_N_Assigned_sendMessage_post[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pNode -> DistrubedTreeSpanning/N/Assigned } } + { pNode -> DistrubedTreeSpanning/N/Assigned } }
  (pNode -> DistrubedTreeSpanning/N. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred DistrubedTreeSpanning_N_Assigned_sendMessage_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, pNode : one Node, scope0 : one StateLabel, scope1 : one StateLabel] {
  { pNode -> DistrubedTreeSpanning/N/Assigned } in sNext. (conf1)
  (s. (stable) = boolean/True => 
    ! {DistrubedTreeSpanning in scope0} and
    ! {{ pNode -> DistrubedTreeSpanning/N } in scope1}
 else {
    boolean/True }
)
}

pred DistrubedTreeSpanning_N_Assigned_sendMessage[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  pNode. (s. (DistrubedTreeSpanning_N_Assigned_sendMessage_pre))
  pNode. (sNext. (s. (DistrubedTreeSpanning_N_Assigned_sendMessage_post)))
}

pred DistrubedTreeSpanning_N_Unassigned_RootAssign_pre[s : one Snapshot, pNode : one Node] {
  { pNode -> DistrubedTreeSpanning/N/Unassigned } in s. (conf1)
  ! {DistrubedTreeSpanning in s. (scopesUsed0)}
  ! {{ pNode -> DistrubedTreeSpanning/N } in s. (scopesUsed1)}
}


pred DistrubedTreeSpanning_N_Unassigned_RootAssign_post[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pNode -> DistrubedTreeSpanning/N/Unassigned } - { pNode -> DistrubedTreeSpanning/N/Assigned } } + { pNode -> DistrubedTreeSpanning/N/Assigned } }
  (pNode -> DistrubedTreeSpanning/N. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred DistrubedTreeSpanning_N_Unassigned_RootAssign_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, pNode : one Node, scope0 : one StateLabel, scope1 : one StateLabel] {
  { pNode -> DistrubedTreeSpanning/N/Unassigned } in sNext. (conf1)
  (s. (stable) = boolean/True => 
    ! {DistrubedTreeSpanning in scope0} and
    ! {{ pNode -> DistrubedTreeSpanning/N } in scope1}
 else {
    boolean/True }
)
}

pred DistrubedTreeSpanning_N_Unassigned_RootAssign[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  pNode. (s. (DistrubedTreeSpanning_N_Unassigned_RootAssign_pre))
  pNode. (sNext. (s. (DistrubedTreeSpanning_N_Unassigned_RootAssign_post)))
}

pred DistrubedTreeSpanning_N_Unassigned_NodeAssign_pre[s : one Snapshot, pNode : one Node] {
  { pNode -> DistrubedTreeSpanning/N/Unassigned } in s. (conf1)
  ! {DistrubedTreeSpanning in s. (scopesUsed0)}
  ! {{ pNode -> DistrubedTreeSpanning/N } in s. (scopesUsed1)}
}


pred DistrubedTreeSpanning_N_Unassigned_NodeAssign_post[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pNode -> DistrubedTreeSpanning/N/Unassigned } - { pNode -> DistrubedTreeSpanning/N/Assigned } } + { pNode -> DistrubedTreeSpanning/N/Assigned } }
  (pNode -> DistrubedTreeSpanning/N. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred DistrubedTreeSpanning_N_Unassigned_NodeAssign_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, pNode : one Node, scope0 : one StateLabel, scope1 : one StateLabel] {
  { pNode -> DistrubedTreeSpanning/N/Unassigned } in sNext. (conf1)
  (s. (stable) = boolean/True => 
    ! {DistrubedTreeSpanning in scope0} and
    ! {{ pNode -> DistrubedTreeSpanning/N } in scope1}
 else {
    boolean/True }
)
}

pred DistrubedTreeSpanning_N_Unassigned_NodeAssign[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  pNode. (s. (DistrubedTreeSpanning_N_Unassigned_NodeAssign_pre))
  pNode. (sNext. (s. (DistrubedTreeSpanning_N_Unassigned_NodeAssign_post)))
}

pred testIfNextStable[s : one Snapshot, sNext : one Snapshot, scope0 : one AllEvents, scope1 : one AllEvents] {
  ! {scope1. (scope0. (sNext. (s. (DistrubedTreeSpanning_N_Assigned_sendMessage_enabledAfterStep))))}
  ! {scope1. (scope0. (sNext. (s. (DistrubedTreeSpanning_N_Unassigned_RootAssign_enabledAfterStep))))}
  ! {scope1. (scope0. (sNext. (s. (DistrubedTreeSpanning_N_Unassigned_NodeAssign_enabledAfterStep))))}
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  (some pNode: one Node | { pNode. (sNext. (s. (DistrubedTreeSpanning_N_Assigned_sendMessage))) or
    pNode. (sNext. (s. (DistrubedTreeSpanning_N_Unassigned_RootAssign))) or
    pNode. (sNext. (s. (DistrubedTreeSpanning_N_Unassigned_NodeAssign))) })
}

