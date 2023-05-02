open util/ordering[Node] as node

open util/boolean
open util/ordering[Snapshot] as Snapshot

abstract sig Status {}
one sig Stabilizing, Rectifying extends Status{}

pred between [n1, nb, n2: Node] {
	     lt[n1,n2] =>   ( lt[n1,nb] && lt[nb,n2] )
             else ( lt[n1,nb] || lt[nb,n2] )  }

// Returns the first node if current node is the last Node in the ordering
fun nextNode [n: Node] : lone Node  {
	{m: Node | no node/next[n] implies m = node/first
		else m = node/next[n]
	}
}

// Returns the previous node in the ordering
fun prevNode [n: Node] : lone Node  {
	{m: Node | no node/prev[n] implies m = node/last
		else m = node/prev[n]
	}
}


fact alwaysThreeMembers {
	all s: Snapshot | {#(s.System_members) >= 3}
}

/******************************************* FUNCTIONS FOR CHECKING PROPERTIES ******************************************/

// Returns a tuple (Node, Node) where the second element is a Live successor of the first element
fun succ [s: Snapshot] : Node -> Node {
	{ m1, m2: s.System_members | m1.(s.System_N_frst) in s.System_members => (m2 = m1.(s.System_N_frst)) else (m2 = m1.(s.System_N_scnd)) }
}

// Returns the members that form a ring
fun ring [s: Snapshot] : some Node { {m: s.System_members | m in m.^(succ[s])} }

fun appendages[s: Snapshot] : set Node { s.System_members - ring[s]  }

/******************************************* PROPERTIES ******************************************/

// Members form atleast one ring
pred atLeastOneRing [s: Snapshot] {
	some ring[s]
}

// Members form atmost one ring
pred atMostOneRing [s: Snapshot] {
	(all m1, m2: ring[s] | m1 in m2.^(succ[s]))
}

// Members are ordered
pred orderedRing[s: Snapshot] { 
	all disj m1, m2, mb: ring[s] |
		m2 = m1.^(succ[s]) implies not between[m1, mb, m2] 
}

// Member successors are ordered
pred orderedSuccessors[s: Snapshot] {
	(all m: s.System_members | between[m, m.(s.System_N_frst), m.(s.System_N_scnd)])
}

pred connectedAppendages[s: Snapshot] {
	(all m1: appendages[s] | some m2: ring[s] | m2 in m1.^(succ[s]))
}

pred valid[s: Snapshot] {
	atLeastOneRing[s]
	atMostOneRing[s]
	orderedSuccessors[s]
	connectedAppendages[s]
	orderedRing[s]
}

assert ideal {
	(one s0: Snapshot | all nexts: nexts[s0] | {
		((System_N_Failed_Join + System_N_Live_Fail) !in Identifiers.(nexts.taken1)) =>
		some s1: nexts | {
			valid[s1]
			no appendages[s1]
			(s1.System_N_frst) = ~(s1.System_N_prdc) }
	})
}

check ideal for exactly 15 Snapshot, exactly 4 Node
check ideal for exactly 15 Snapshot, exactly 5 Node
abstract sig StateLabel {}
sig System extends StateLabel {} 
one sig System_N extends System {} 
one sig System_N_Live extends System_N {} 
one sig System_N_Failed extends System_N {} 

abstract sig Identifiers {}
sig Node extends Identifiers {} 

sig Snapshot {
  scopesUsed0 : set StateLabel,
  conf0 : set StateLabel,
  scopesUsed1 : Identifiers -> Identifiers -> StateLabel,
  conf1 : Identifiers -> Identifiers -> StateLabel,
  stable : one boolean/Bool
}

pred System_N_Live_StabilizeFromPrdc_pre[s : one Snapshot, pNode : one Node] {
  { pNode -> System/N/Live } in s. (conf1)
  ! {System in s. (scopesUsed0)}
  ! {{ pNode -> System/N } in s. (scopesUsed1)}
}


pred System_N_Live_StabilizeFromPrdc_post[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pNode -> System/N/Live } } + { pNode -> System/N/Live } }
  (pNode -> System/N. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_N_Live_StabilizeFromPrdc_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, pNode : one Node, scope0 : one StateLabel, scope1 : one StateLabel] {
  { pNode -> System/N/Live } in sNext. (conf1)
  (s. (stable) = boolean/True => 
    ! {System in scope0} and
    ! {{ pNode -> System/N } in scope1}
 else {
    boolean/True }
)
}

pred System_N_Live_StabilizeFromPrdc[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  pNode. (s. (System_N_Live_StabilizeFromPrdc_pre))
  pNode. (sNext. (s. (System_N_Live_StabilizeFromPrdc_post)))
}

pred System_N_Live_Flush_pre[s : one Snapshot, pNode : one Node] {
  { pNode -> System/N/Live } in s. (conf1)
  ! {System in s. (scopesUsed0)}
  ! {{ pNode -> System/N } in s. (scopesUsed1)}
}


pred System_N_Live_Flush_post[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pNode -> System/N/Live } } + { pNode -> System/N/Live } }
  (pNode -> System/N. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_N_Live_Flush_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, pNode : one Node, scope0 : one StateLabel, scope1 : one StateLabel] {
  { pNode -> System/N/Live } in sNext. (conf1)
  (s. (stable) = boolean/True => 
    ! {System in scope0} and
    ! {{ pNode -> System/N } in scope1}
 else {
    boolean/True }
)
}

pred System_N_Live_Flush[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  pNode. (s. (System_N_Live_Flush_pre))
  pNode. (sNext. (s. (System_N_Live_Flush_post)))
}

pred System_N_Live_Fail_pre[s : one Snapshot, pNode : one Node] {
  { pNode -> System/N/Live } in s. (conf1)
  ! {System in s. (scopesUsed0)}
  ! {{ pNode -> System/N } in s. (scopesUsed1)}
}


pred System_N_Live_Fail_post[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pNode -> System/N/Live } - { pNode -> System/N/Failed } } + { pNode -> System/N/Failed } }
  (pNode -> System/N. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_N_Live_Fail_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, pNode : one Node, scope0 : one StateLabel, scope1 : one StateLabel] {
  { pNode -> System/N/Live } in sNext. (conf1)
  (s. (stable) = boolean/True => 
    ! {System in scope0} and
    ! {{ pNode -> System/N } in scope1}
 else {
    boolean/True }
)
}

pred System_N_Live_Fail[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  pNode. (s. (System_N_Live_Fail_pre))
  pNode. (sNext. (s. (System_N_Live_Fail_post)))
}

pred System_N_Live_StabilizeFromSucc_pre[s : one Snapshot, pNode : one Node] {
  { pNode -> System/N/Live } in s. (conf1)
  ! {System in s. (scopesUsed0)}
  ! {{ pNode -> System/N } in s. (scopesUsed1)}
}


pred System_N_Live_StabilizeFromSucc_post[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pNode -> System/N/Live } } + { pNode -> System/N/Live } }
  (pNode -> System/N. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_N_Live_StabilizeFromSucc_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, pNode : one Node, scope0 : one StateLabel, scope1 : one StateLabel] {
  { pNode -> System/N/Live } in sNext. (conf1)
  (s. (stable) = boolean/True => 
    ! {System in scope0} and
    ! {{ pNode -> System/N } in scope1}
 else {
    boolean/True }
)
}

pred System_N_Live_StabilizeFromSucc[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  pNode. (s. (System_N_Live_StabilizeFromSucc_pre))
  pNode. (sNext. (s. (System_N_Live_StabilizeFromSucc_post)))
}

pred System_N_Live_Rectify_pre[s : one Snapshot, pNode : one Node] {
  { pNode -> System/N/Live } in s. (conf1)
  ! {System in s. (scopesUsed0)}
  ! {{ pNode -> System/N } in s. (scopesUsed1)}
}


pred System_N_Live_Rectify_post[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pNode -> System/N/Live } } + { pNode -> System/N/Live } }
  (pNode -> System/N. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_N_Live_Rectify_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, pNode : one Node, scope0 : one StateLabel, scope1 : one StateLabel] {
  { pNode -> System/N/Live } in sNext. (conf1)
  (s. (stable) = boolean/True => 
    ! {System in scope0} and
    ! {{ pNode -> System/N } in scope1}
 else {
    boolean/True }
)
}

pred System_N_Live_Rectify[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  pNode. (s. (System_N_Live_Rectify_pre))
  pNode. (sNext. (s. (System_N_Live_Rectify_post)))
}

pred System_N_Failed_Join_pre[s : one Snapshot, pNode : one Node] {
  { pNode -> System/N/Failed } in s. (conf1)
  ! {System in s. (scopesUsed0)}
  ! {{ pNode -> System/N } in s. (scopesUsed1)}
}


pred System_N_Failed_Join_post[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { pNode -> System/N/Live } - { pNode -> System/N/Failed } } + { pNode -> System/N/Live } }
  (pNode -> System/N. (none. (sNext. (s. (testIfNextStable)))) => 
    sNext. (stable) = boolean/True and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } )
 else {
    sNext. (stable) = boolean/False and
    (s. (stable) = boolean/True =>  boolean/True  else { boolean/True } ) }
)
}

pred System_N_Failed_Join_enabledAfterStep[s : one Snapshot, sNext : one Snapshot, pNode : one Node, scope0 : one StateLabel, scope1 : one StateLabel] {
  { pNode -> System/N/Failed } in sNext. (conf1)
  (s. (stable) = boolean/True => 
    ! {System in scope0} and
    ! {{ pNode -> System/N } in scope1}
 else {
    boolean/True }
)
}

pred System_N_Failed_Join[s : one Snapshot, sNext : one Snapshot, pNode : one Node] {
  pNode. (s. (System_N_Failed_Join_pre))
  pNode. (sNext. (s. (System_N_Failed_Join_post)))
}

pred testIfNextStable[s : one Snapshot, sNext : one Snapshot, scope0 : one AllEvents, scope1 : one AllEvents] {
  ! {scope1. (scope0. (sNext. (s. (System_N_Live_StabilizeFromPrdc_enabledAfterStep))))}
  ! {scope1. (scope0. (sNext. (s. (System_N_Live_Flush_enabledAfterStep))))}
  ! {scope1. (scope0. (sNext. (s. (System_N_Live_Fail_enabledAfterStep))))}
  ! {scope1. (scope0. (sNext. (s. (System_N_Live_StabilizeFromSucc_enabledAfterStep))))}
  ! {scope1. (scope0. (sNext. (s. (System_N_Live_Rectify_enabledAfterStep))))}
  ! {scope1. (scope0. (sNext. (s. (System_N_Failed_Join_enabledAfterStep))))}
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  (some pNode: one Node | { pNode. (sNext. (s. (System_N_Live_StabilizeFromPrdc))) or
    pNode. (sNext. (s. (System_N_Live_Flush))) or
    pNode. (sNext. (s. (System_N_Live_Fail))) or
    pNode. (sNext. (s. (System_N_Live_StabilizeFromSucc))) or
    pNode. (sNext. (s. (System_N_Live_Rectify))) or
    pNode. (sNext. (s. (System_N_Failed_Join))) })
}

