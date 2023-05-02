open util/ring[Identifier] as P0


assert eventuallyLeaderElected {
	some s: Snapshot | some s.System_elected
}

assert electedHasHighestIdentifier {
    (one s: one Snapshot | one s.System_elected and (s.System_elected) in P0/last)
}

check eventuallyLeaderElected for exactly 13 Snapshot, exactly 6 Identifier, exactly 6 token
check eventuallyLeaderElected for 15 Snapshot, exactly 7 Identifier, exactly 7 token
check electedHasHighestIdentifier for 13 Snapshot, exactly 6 Identifier, exactly 6 token
check electedHasHighestIdentifier for 15 Snapshot, exactly 7 Identifier, exactly 7 token

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
  ! {System in scopesUsed0}
  ! {{ pIdentifier -> System/Process } in scopesUsed1}
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

pred System_Process_Electing_ConsumeToken_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pIdentifier -> System/Process/Electing } in sNext. (conf1)
}

pred System_Process_Electing_ConsumeToken[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (System_Process_Electing_ConsumeToken_pre))
  pIdentifier. (sNext. (s. (System_Process_Electing_ConsumeToken_post)))
}

pred System_Process_Electing_PassToken_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> System/Process/Electing } in s. (conf1)
  ! {System in scopesUsed0}
  ! {{ pIdentifier -> System/Process } in scopesUsed1}
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

pred System_Process_Electing_PassToken_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pIdentifier -> System/Process/Electing } in sNext. (conf1)
}

pred System_Process_Electing_PassToken[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (System_Process_Electing_PassToken_pre))
  pIdentifier. (sNext. (s. (System_Process_Electing_PassToken_post)))
}

pred System_Process_Electing_ElectLeader_pre[s : one Snapshot, pIdentifier : one Identifier] {
  { pIdentifier -> System/Process/Electing } in s. (conf1)
  ! {System in scopesUsed0}
  ! {{ pIdentifier -> System/Process } in scopesUsed1}
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

pred System_Process_Electing_ElectLeader_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  { pIdentifier -> System/Process/Electing } in sNext. (conf1)
}

pred System_Process_Electing_ElectLeader[s : one Snapshot, sNext : one Snapshot, pIdentifier : one Identifier] {
  pIdentifier. (s. (System_Process_Electing_ElectLeader_pre))
  pIdentifier. (sNext. (s. (System_Process_Electing_ElectLeader_post)))
}

pred testIfNextStable[s : one Snapshot, sNext : one Snapshot, scopesUsed0 : one StateLabel, scopesUsed1 : one StateLabel] {
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Process_Electing_ConsumeToken_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Process_Electing_PassToken_enabledAfterStep))))}
  ! {scopesUsed1. (scopesUsed0. (sNext. (s. (System_Process_Electing_ElectLeader_enabledAfterStep))))}
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  (some pIdentifier: one Identifier | { pIdentifier. (sNext. (s. (System_Process_Electing_ConsumeToken))) or
    pIdentifier. (sNext. (s. (System_Process_Electing_PassToken))) or
    pIdentifier. (sNext. (s. (System_Process_Electing_ElectLeader))) })
}

