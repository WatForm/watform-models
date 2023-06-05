/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-05 14:19:49
*/

open util/ordering[Node] as node

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

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

abstract sig DshStates {}
abstract sig System extends DshStates {} 
abstract sig System_N extends System {} 
one sig System_N_Live extends System_N {} 
one sig System_N_Failed extends System_N {} 

abstract sig DshIds {}
sig Node extends DshIds {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_sc_used1: DshIds -> DshStates,
  dsh_conf1: DshIds -> DshStates,
  dsh_stable: one boolean/Bool,
  System_N_frst: Node -> lone Node,
  System_N_scnd: Node -> lone Node,
  System_N_prdc: Node -> lone Node,
  System_N_status: Node -> Status,
  System_N_saved: Node -> lone Node,
  System_members: Node
}

pred dsh_initial [
	s: one DshSnapshot] {
  (all p0_Node: one
  Node | (s.dsh_conf0) = none and
           (s.dsh_conf1) = (Node -> System_N_Live) and
           (s.dsh_sc_used1) = (none -> none) and
           no
           p0_Node.(s.System_N_status) and
           no
           p0_Node.(s.System_N_saved) and
           (p0_Node.(s.System_N_frst)) = (p0_Node.nextNode) and
           (p0_Node.(s.System_N_scnd)) =
             ((p0_Node.(s.System_N_frst)).nextNode) and
           (p0_Node.(s.System_N_prdc)) = (p0_Node.prevNode) and
           Node in s.System_members)
  (s.dsh_stable).boolean/isTrue
}

pred System_N_Live_StabilizeFromPrdc_pre [
	s: one DshSnapshot,
	p0_Node: one Node] {
  some ((p0_Node -> System_N_Live) & (s.dsh_conf1))
  p0_Node in s.System_members and
  (p0_Node.(s.System_N_status)) = Stabilizing and
  (p0_Node.(s.System_N_frst)).((p0_Node.(s.System_N_saved)).(p0_Node.between))
  !(System in (s.dsh_sc_used0))
  !((p0_Node -> System_N) in (s.dsh_sc_used1))
}


pred System_N_Live_StabilizeFromPrdc_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) - (p0_Node -> System_N_Live)) +
     (p0_Node -> System_N_Live))
  no
  p0_Node.(sn.System_N_status) and
  no
  p0_Node.(sn.System_N_saved) and
  (p0_Node.(s.System_N_saved) !in s.System_members)=>
      (p0_Node.(sn.System_N_frst)) =
        (p0_Node.(s.System_N_frst)) and
        (p0_Node.(sn.System_N_scnd)) =
          (p0_Node.(s.System_N_scnd)) and
        (all n: Node - p0_Node | (n.(sn.System_N_status)) =
                                   (n.(s.System_N_status))) and
        (all n: Node - p0_Node | (n.(sn.System_N_saved)) =
                                   (n.(s.System_N_saved)))
    else
      (p0_Node.(sn.System_N_frst)) =
        (p0_Node.(s.System_N_saved)) and
        (p0_Node.(sn.System_N_scnd)) =
          ((p0_Node.(s.System_N_saved)).(s.System_N_frst)) and
        ((p0_Node.(s.System_N_saved)).(sn.System_N_status)) =
          Rectifying and
        ((p0_Node.(s.System_N_saved)).(sn.System_N_saved)) =
          p0_Node and
        (all n: (Node - (p0_Node.(s.System_N_saved))) -
                  p0_Node | (n.(sn.System_N_status)) =
                              (n.(s.System_N_status))) and
        (all n: (Node - (p0_Node.(s.System_N_saved))) -
                  p0_Node | (n.(sn.System_N_saved)) =
                              (n.(s.System_N_saved)))
  
  ((p0_Node -> System_N).(none.(p0_Node.(sn.(s._testIfNextStable)))))=>
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
                ((s.dsh_sc_used1) + (p0_Node -> System_N)))
       )

}

pred System_N_Live_StabilizeFromPrdc_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some ((p0_Node -> System_N_Live) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_Node -> System_N) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_N_Live_StabilizeFromPrdc [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  p0_Node.(s.System_N_Live_StabilizeFromPrdc_pre)
  p0_Node.(sn.(s.System_N_Live_StabilizeFromPrdc_post))
}

pred System_N_Live_Flush_pre [
	s: one DshSnapshot,
	p0_Node: one Node] {
  some ((p0_Node -> System_N_Live) & (s.dsh_conf1))
  p0_Node in s.System_members and
  p0_Node.(s.System_N_prdc) !in s.System_members
  !(System in (s.dsh_sc_used0))
  !((p0_Node -> System_N) in (s.dsh_sc_used1))
}


pred System_N_Live_Flush_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) - (p0_Node -> System_N_Live)) +
     (p0_Node -> System_N_Live))
  (p0_Node.(sn.System_N_prdc)) = none
  ((p0_Node -> System_N).(none.(p0_Node.(sn.(s._testIfNextStable)))))=>
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
                ((s.dsh_sc_used1) + (p0_Node -> System_N)))
       )

}

pred System_N_Live_Flush_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some ((p0_Node -> System_N_Live) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_Node -> System_N) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_N_Live_Flush [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  p0_Node.(s.System_N_Live_Flush_pre)
  p0_Node.(sn.(s.System_N_Live_Flush_post))
}

pred System_N_Live_Fail_pre [
	s: one DshSnapshot,
	p0_Node: one Node] {
  some ((p0_Node -> System_N_Live) & (s.dsh_conf1))
  (all n: Node - p0_Node | some
  (((s.System_members) - p0_Node) &
     ((n.(s.System_N_frst)) + (n.(s.System_N_scnd)))))
  !(System in (s.dsh_sc_used0))
  !((p0_Node -> System_N) in (s.dsh_sc_used1))
}


pred System_N_Live_Fail_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) - (p0_Node -> System_N_Live)) -
      (p0_Node -> System_N_Failed)) +
     (p0_Node -> System_N_Failed))
  (sn.System_members) = ((s.System_members) - p0_Node) and
  (p0_Node.(sn.System_N_frst)) = none and
  (p0_Node.(sn.System_N_scnd)) = none and
  (p0_Node.(sn.System_N_prdc)) = none and
  (p0_Node.(sn.System_N_status)) = none
  ((p0_Node -> System_N).(none.(p0_Node.(sn.(s._testIfNextStable)))))=>
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
                ((s.dsh_sc_used1) + (p0_Node -> System_N)))
       )

}

pred System_N_Live_Fail_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some ((p0_Node -> System_N_Live) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_Node -> System_N) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_N_Live_Fail [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  p0_Node.(s.System_N_Live_Fail_pre)
  p0_Node.(sn.(s.System_N_Live_Fail_post))
}

pred System_N_Live_StabilizeFromSucc_pre [
	s: one DshSnapshot,
	p0_Node: one Node] {
  some ((p0_Node -> System_N_Live) & (s.dsh_conf1))
  no p0_Node.(s.System_N_status)
  !(System in (s.dsh_sc_used0))
  !((p0_Node -> System_N) in (s.dsh_sc_used1))
}


pred System_N_Live_StabilizeFromSucc_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) - (p0_Node -> System_N_Live)) +
     (p0_Node -> System_N_Live))
  (p0_Node.(s.System_N_frst) !in s.System_members)=>
    (p0_Node.(sn.System_N_frst)) =
      (p0_Node.(s.System_N_scnd)) and
      (p0_Node.(sn.System_N_scnd)) =
        ((p0_Node.(s.System_N_scnd)).nextNode) and
      (all n: Node | (n.(sn.System_N_status)) =
                       (n.(s.System_N_status))) and
      (all n: Node | (n.(sn.System_N_saved)) =
                       (n.(s.System_N_saved)))
  else
    (p0_Node.(sn.System_N_frst)) =
      (p0_Node.(s.System_N_frst)) and
      (p0_Node.(sn.System_N_scnd)) =
        ((p0_Node.(s.System_N_frst)).(s.System_N_frst)) and
      (some
         (p0_Node.(s.System_N_frst)).(s.System_N_prdc) and
         (p0_Node.(s.System_N_frst)).(((p0_Node.(s.System_N_frst)).(s.System_N_prdc)).(p0_Node.between)) and
         (p0_Node.(s.System_N_frst)).(s.System_N_prdc) in
           s.System_members)=>
          (p0_Node.(sn.System_N_status)) = Stabilizing and
            (p0_Node.(sn.System_N_saved)) =
              ((p0_Node.(s.System_N_frst)).(s.System_N_prdc)) and
            (all n: Node - p0_Node | (n.(sn.System_N_status)) =
                                       (n.(s.System_N_status))) and
            (all n: Node - p0_Node | (n.(sn.System_N_saved)) =
                                       (n.(s.System_N_saved)))
        else
          ((p0_Node !in
              (p0_Node.(s.System_N_frst)).(s.System_N_prdc))=>
               ((p0_Node.(s.System_N_frst)).(sn.System_N_status)) =
                 Rectifying and
                 ((p0_Node.(s.System_N_frst)).(sn.System_N_saved)) =
                   p0_Node and
                 (all n: Node - (p0_Node.(s.System_N_frst)) | (n.(sn.System_N_status)) =
                                                                (n.(s.System_N_status))) and
                 (all n: Node - (p0_Node.(s.System_N_frst)) | (n.(sn.System_N_saved)) =
                                                                (n.(s.System_N_saved)))
             else
               (all n: Node | (n.(sn.System_N_status)) =
                                (n.(s.System_N_status))) and
                 (all n: Node | (n.(sn.System_N_saved)) =
                                  (n.(s.System_N_saved)))
           )
      

  ((p0_Node -> System_N).(none.(p0_Node.(sn.(s._testIfNextStable)))))=>
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
                ((s.dsh_sc_used1) + (p0_Node -> System_N)))
       )

}

pred System_N_Live_StabilizeFromSucc_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some ((p0_Node -> System_N_Live) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_Node -> System_N) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_N_Live_StabilizeFromSucc [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  p0_Node.(s.System_N_Live_StabilizeFromSucc_pre)
  p0_Node.(sn.(s.System_N_Live_StabilizeFromSucc_post))
}

pred System_N_Live_Rectify_pre [
	s: one DshSnapshot,
	p0_Node: one Node] {
  some ((p0_Node -> System_N_Live) & (s.dsh_conf1))
  p0_Node in s.System_members and
  (p0_Node.(s.System_N_status)) = Rectifying
  !(System in (s.dsh_sc_used0))
  !((p0_Node -> System_N) in (s.dsh_sc_used1))
}


pred System_N_Live_Rectify_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) - (p0_Node -> System_N_Live)) +
     (p0_Node -> System_N_Live))
  ({ p0_Node.((p0_Node.(s.System_N_saved)).((p0_Node.(s.System_N_prdc)).between)) or
     p0_Node.(s.System_N_prdc) !in s.System_members or
     no
     p0_Node.(s.System_N_prdc) })=>
    (p0_Node.(sn.System_N_prdc)) =
      (p0_Node.(s.System_N_saved))
  else
    (p0_Node.(sn.System_N_prdc)) =
      (p0_Node.(s.System_N_prdc))

  ((p0_Node -> System_N).(none.(p0_Node.(sn.(s._testIfNextStable)))))=>
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
                ((s.dsh_sc_used1) + (p0_Node -> System_N)))
       )

}

pred System_N_Live_Rectify_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some ((p0_Node -> System_N_Live) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_Node -> System_N) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_N_Live_Rectify [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  p0_Node.(s.System_N_Live_Rectify_pre)
  p0_Node.(sn.(s.System_N_Live_Rectify_post))
}

pred System_N_Failed_Join_pre [
	s: one DshSnapshot,
	p0_Node: one Node] {
  some ((p0_Node -> System_N_Failed) & (s.dsh_conf1))
  p0_Node !in s.System_members
  !(System in (s.dsh_sc_used0))
  !((p0_Node -> System_N) in (s.dsh_sc_used1))
}


pred System_N_Failed_Join_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  ((((s.dsh_conf1) - (p0_Node -> System_N_Live)) -
      (p0_Node -> System_N_Failed)) +
     (p0_Node -> System_N_Live))
  (sn.System_members) = ((s.System_members) + p0_Node)
  ((p0_Node -> System_N).(none.(p0_Node.(sn.(s._testIfNextStable)))))=>
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
                ((s.dsh_sc_used1) + (p0_Node -> System_N)))
       )

}

pred System_N_Failed_Join_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  some ((p0_Node -> System_N_Failed) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue and
    !(System in dsh_scp0) and
    !((p0_Node -> System_N) in dsh_scp1) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_N_Failed_Join [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  p0_Node.(s.System_N_Failed_Join_pre)
  p0_Node.(sn.(s.System_N_Failed_Join_post))
}

pred _testIfNextStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	dsh_scp0: DshStates,
	dsh_scp1: DshIds -> DshStates] {
  !(dsh_scp1.(dsh_scp0.(p0_Node.(sn.(s.System_N_Live_StabilizeFromPrdc_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_Node.(sn.(s.System_N_Live_Flush_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_Node.(sn.(s.System_N_Live_Fail_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_Node.(sn.(s.System_N_Live_StabilizeFromSucc_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_Node.(sn.(s.System_N_Live_Rectify_enabledAfterStep)))))
  !(dsh_scp1.(dsh_scp0.(p0_Node.(sn.(s.System_N_Failed_Join_enabledAfterStep)))))
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (some p0_Node: one
  Node | { p0_Node.(sn.(s.System_N_Live_StabilizeFromPrdc)) or
             p0_Node.(sn.(s.System_N_Live_Flush)) or
             p0_Node.(sn.(s.System_N_Live_Fail)) or
             p0_Node.(sn.(s.System_N_Live_StabilizeFromSucc)) or
             p0_Node.(sn.(s.System_N_Live_Rectify)) or
             p0_Node.(sn.(s.System_N_Failed_Join)) })
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}


