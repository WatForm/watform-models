open util/ordering[Identifier] as P0

open util/boolean
open util/ordering[Snapshot] as Snapshot
open util/buffer[bufIdx0, Identifier] as token

// Returns the first node if current node is the last Node in the ordering
fun nextProcess [ie: Identifier] : lone Identifier  {
	{m: Identifier | no P0/next[ie] implies m = P0/first
		else m = P0/next[ie]
	}
}


assert ctl_eventuallyLeaderElected {
	ctl_mc[af[{s: Snapshot | some s.System_elected}]]
}

assert ctl_electedHasHighestIdentifier {
    ctl_mc[af[{s: one Snapshot | some s.System_elected => (s.System_elected) in P0/last}]]
}

check ctl_electedHasHighestIdentifier for exactly 13 Snapshot, exactly 6 Identifier, exactly 6 token, 1 PathNode
check ctl_electedHasHighestIdentifier for exactly 15 Snapshot, exactly 7 Identifier, exactly 7 token, 1 PathNode
abstract sig StateLabel {}
sig System extends StateLabel {} 
one sig System_Process extends System {} 
one sig System_Process_Electing extends System_Process {} 
one sig System_Process_Elected extends System_Process {} 

abstract sig Identifiers {}
sig Identifier extends Identifiers {} 

sig Snapshot {
  scopesUsed0 : set StateLabel,
  conf0 : set StateLabel,
  scopesUsed1 : Identifiers -> Identifiers -> StateLabel,
  conf1 : Identifiers -> Identifiers -> StateLabel,
  stable : one boolean/Bool
}

pred System_Process_Electing_ConsumeToken_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> System/Process/Electing } in s. (conf1)
  ! {System in s. (scopesUsed0)}
  ! {{ pIdentifier -> System/Process } in s. (scopesUsed1)}
}


pred System_Process_Electing_ConsumeToken_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> System/Process/Electing } } + { pIdentifier -> System/Process/Electing } }
  (pIdentifier -> System/Process. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Process_Electing_ConsumeToken_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier, scope0 : one StateLabel, scope1 : one StateLabel] {
  { pIdentifier -> System/Process/Electing } in sNext. (conf1)
  (s. (stable) = boolean/True => 
    ! {System in scope0} and
    ! {{ pIdentifier -> System/Process } in scope1}
 else {
    boolean/True }
)
}

pred System_Process_Electing_ConsumeToken[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (System_Process_Electing_ConsumeToken_pre))
  pIdentifier. (sNext. (s. (System_Process_Electing_ConsumeToken_post)))
}

pred System_Process_Electing_PassToken_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> System/Process/Electing } in s. (conf1)
  ! {System in s. (scopesUsed0)}
  ! {{ pIdentifier -> System/Process } in s. (scopesUsed1)}
}


pred System_Process_Electing_PassToken_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> System/Process/Electing } } + { pIdentifier -> System/Process/Electing } }
  (pIdentifier -> System/Process. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Process_Electing_PassToken_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier, scope0 : one StateLabel, scope1 : one StateLabel] {
  { pIdentifier -> System/Process/Electing } in sNext. (conf1)
  (s. (stable) = boolean/True => 
    ! {System in scope0} and
    ! {{ pIdentifier -> System/Process } in scope1}
 else {
    boolean/True }
)
}

pred System_Process_Electing_PassToken[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (System_Process_Electing_PassToken_pre))
  pIdentifier. (sNext. (s. (System_Process_Electing_PassToken_post)))
}

pred System_Process_Electing_ElectLeader_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> System/Process/Electing } in s. (conf1)
  ! {System in s. (scopesUsed0)}
  ! {{ pIdentifier -> System/Process } in s. (scopesUsed1)}
}


pred System_Process_Electing_ElectLeader_post[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pIdentifier -> System/Process/Electing } - { pIdentifier -> System/Process/Elected } } + { pIdentifier -> System/Process/Elected } }
  (pIdentifier -> System/Process. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_Process_Electing_ElectLeader_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier, scope0 : one StateLabel, scope1 : one StateLabel] {
  { pIdentifier -> System/Process/Electing } in sNext. (conf1)
  (s. (stable) = boolean/True => 
    ! {System in scope0} and
    ! {{ pIdentifier -> System/Process } in scope1}
 else {
    boolean/True }
)
}

pred System_Process_Electing_ElectLeader[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (System_Process_Electing_ElectLeader_pre))
  pIdentifier. (sNext. (s. (System_Process_Electing_ElectLeader_post)))
}

pred testIfNextStable[s : one Snapshot, sNext : one Snapshot, scope0 : one AllEvents, scope1 : one AllEvents] {
  ! {scope1. (scope0. (sNext. (s. (System_Process_Electing_ConsumeToken_enabledAfterStep))))}
  ! {scope1. (scope0. (sNext. (s. (System_Process_Electing_PassToken_enabledAfterStep))))}
  ! {scope1. (scope0. (sNext. (s. (System_Process_Electing_ElectLeader_enabledAfterStep))))}
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  (some pIdentifier: one Identifier | { pIdentifier. (sNext. (s. (System_Process_Electing_ConsumeToken))) or
    pIdentifier. (sNext. (s. (System_Process_Electing_PassToken))) or
    pIdentifier. (sNext. (s. (System_Process_Electing_ElectLeader))) })
}

