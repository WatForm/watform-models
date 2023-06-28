/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-28 18:42:19
*/

open util/ordering[Node] as node

open util/boolean
open util/tcmc[DshSnapshot]

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
abstract sig DshScopes {}
one sig SystemScope extends DshScopes {} 
one sig System_NScope extends DshScopes {} 
abstract sig System_N extends System {} 
one sig System_N_LiveScope extends DshScopes {} 
one sig System_N_Live extends System_N {} 
one sig System_N_FailedScope extends DshScopes {} 
one sig System_N_Failed extends System_N {} 

abstract sig Transitions {}
one sig NO_TRANS extends Transitions {} 
one sig System_N_Live_StabilizeFromPrdc extends Transitions {} 
one sig System_N_Live_Flush extends Transitions {} 
one sig System_N_Live_Fail extends Transitions {} 
one sig System_N_Live_StabilizeFromSucc extends Transitions {} 
one sig System_N_Live_Rectify extends Transitions {} 
one sig System_N_Failed_Join extends Transitions {} 

abstract sig DshIds {}
sig Node extends DshIds {} 

sig DshSnapshot {
  dsh_sc_used0: set DshScopes,
  dsh_conf0: set DshStates,
  dsh_taken0: set Transitions,
  dsh_sc_used1: DshIds -> DshScopes,
  dsh_conf1: DshIds -> DshStates,
  dsh_taken1: DshIds -> Transitions,
  dsh_stable: one boolean/Bool,
  System_N_frst: Node -> lone Node,
  System_N_scnd: Node -> lone Node,
  System_N_prdc: Node -> lone Node,
  System_N_status: Node -> lone Status,
  System_N_saved: Node -> lone Node,
  System_members: set Node
}

pred dsh_initial [
	s: one DshSnapshot] {
  (all p0_Node: one
  Node | (s.dsh_conf0) = none &&
           (s.dsh_conf1) = (Node -> System_N_Live) &&
           (s.dsh_sc_used0) = none &&
           (s.dsh_taken0) = NO_TRANS &&
           (s.dsh_sc_used1) = (none -> none) &&
           (s.dsh_taken1) = (none -> none) &&
           no
           p0_Node.(s.System_N_status) &&
           no
           p0_Node.(s.System_N_saved) &&
           (p0_Node.(s.System_N_frst)) = (p0_Node.nextNode) &&
           (p0_Node.(s.System_N_scnd)) =
             ((p0_Node.(s.System_N_frst)).nextNode) &&
           (p0_Node.(s.System_N_prdc)) = (p0_Node.prevNode) &&
           Node in s.System_members)
  (s.dsh_stable).boolean/isTrue
}

pred System_N_Live_StabilizeFromPrdc_pre [
	s: one DshSnapshot,
	p0_Node: one Node] {
  some ((p0_Node -> System_N_Live) & (s.dsh_conf1))
  p0_Node in s.System_members &&
  (p0_Node.(s.System_N_status)) = Stabilizing &&
  (p0_Node.(s.System_N_frst)).((p0_Node.(s.System_N_saved)).(p0_Node.between))
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_Node -> System_NScope) in (s.dsh_sc_used1))
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
  p0_Node.(sn.System_N_status) &&
  no
  p0_Node.(sn.System_N_saved) &&
  {(p0_Node.(s.System_N_saved) !in s.System_members)=>
      (p0_Node.(sn.System_N_frst)) =
        (p0_Node.(s.System_N_frst)) &&
        (p0_Node.(sn.System_N_scnd)) =
          (p0_Node.(s.System_N_scnd)) &&
        (all n: Node - p0_Node | (n.(sn.System_N_status)) =
                                   (n.(s.System_N_status))) &&
        (all n: Node - p0_Node | (n.(sn.System_N_saved)) =
                                   (n.(s.System_N_saved)))
    else
      (p0_Node.(sn.System_N_frst)) =
        (p0_Node.(s.System_N_saved)) &&
        (p0_Node.(sn.System_N_scnd)) =
          ((p0_Node.(s.System_N_saved)).(s.System_N_frst)) &&
        ((p0_Node.(s.System_N_saved)).(sn.System_N_status)) =
          Rectifying &&
        ((p0_Node.(s.System_N_saved)).(sn.System_N_saved)) =
          p0_Node &&
        (all n: (Node - (p0_Node.(s.System_N_saved))) -
                  p0_Node | (n.(sn.System_N_status)) =
                              (n.(s.System_N_status))) &&
        (all n: (Node - (p0_Node.(s.System_N_saved))) -
                  p0_Node | (n.(sn.System_N_saved)) =
                              (n.(s.System_N_saved)))}
  
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Node -> System_N_Live_StabilizeFromPrdc)
  (all Node_aa: Node - p0_Node | (Node_aa.(s.System_N_frst)) =
                                 (Node_aa.(sn.System_N_frst)))
  (all Node_aa: Node - p0_Node | (Node_aa.(s.System_N_scnd)) =
                                 (Node_aa.(sn.System_N_scnd)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_prdc)) =
           (Node_aa.(sn.System_N_prdc)))
  (s.System_members) = (sn.System_members)
  {((p0_Node -> System_N).(none.(p0_Node.(sn.(s._nextIsStable)))))=>
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
                   (p0_Node -> System_NScope)))}
       )}

}

pred System_N_Live_StabilizeFromPrdc_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some ((p0_Node -> System_N_Live) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_Node -> System_N) in sc1) ||
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
  p0_Node in s.System_members &&
  p0_Node.(s.System_N_prdc) !in s.System_members
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_Node -> System_NScope) in (s.dsh_sc_used1))
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
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) = (p0_Node -> System_N_Live_Flush)
  (all Node_aa: Node - p0_Node | (Node_aa.(s.System_N_prdc)) =
                                 (Node_aa.(sn.System_N_prdc)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_status)) =
           (Node_aa.(sn.System_N_status)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_saved)) =
           (Node_aa.(sn.System_N_saved)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_frst)) =
           (Node_aa.(sn.System_N_frst)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_scnd)) =
           (Node_aa.(sn.System_N_scnd)))
  (s.System_members) = (sn.System_members)
  {((p0_Node -> System_N).(none.(p0_Node.(sn.(s._nextIsStable)))))=>
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
                   (p0_Node -> System_NScope)))}
       )}

}

pred System_N_Live_Flush_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some ((p0_Node -> System_N_Live) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_Node -> System_N) in sc1) ||
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
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_Node -> System_NScope) in (s.dsh_sc_used1))
}


pred System_N_Live_Fail_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_Node -> System_N_Live) +
         (p0_Node -> System_N_Failed))) +
     (p0_Node -> System_N_Failed))
  (sn.System_members) = ((s.System_members) - p0_Node) &&
  (p0_Node.(sn.System_N_frst)) = none &&
  (p0_Node.(sn.System_N_scnd)) = none &&
  (p0_Node.(sn.System_N_prdc)) = none &&
  (p0_Node.(sn.System_N_status)) = none
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) = (p0_Node -> System_N_Live_Fail)
  (all Node_aa: Node - p0_Node | (Node_aa.(s.System_N_status)) =
                                 (Node_aa.(sn.System_N_status)))
  (all Node_aa: Node - p0_Node | (Node_aa.(s.System_N_frst)) =
                                 (Node_aa.(sn.System_N_frst)))
  (all Node_aa: Node - p0_Node | (Node_aa.(s.System_N_scnd)) =
                                 (Node_aa.(sn.System_N_scnd)))
  (all Node_aa: Node - p0_Node | (Node_aa.(s.System_N_prdc)) =
                                 (Node_aa.(sn.System_N_prdc)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_saved)) =
           (Node_aa.(sn.System_N_saved)))
  {((p0_Node -> System_N).(none.(p0_Node.(sn.(s._nextIsStable)))))=>
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
                   (p0_Node -> System_NScope)))}
       )}

}

pred System_N_Live_Fail_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some ((p0_Node -> System_N_Live) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_Node -> System_N) in sc1) ||
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
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_Node -> System_NScope) in (s.dsh_sc_used1))
}


pred System_N_Live_StabilizeFromSucc_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) - (p0_Node -> System_N_Live)) +
     (p0_Node -> System_N_Live))
  {(p0_Node.(s.System_N_frst) !in s.System_members)=>
    (p0_Node.(sn.System_N_frst)) =
      (p0_Node.(s.System_N_scnd)) &&
      (p0_Node.(sn.System_N_scnd)) =
        ((p0_Node.(s.System_N_scnd)).nextNode) &&
      (all n: Node | (n.(sn.System_N_status)) =
                       (n.(s.System_N_status))) &&
      (all n: Node | (n.(sn.System_N_saved)) =
                       (n.(s.System_N_saved)))
  else
    (p0_Node.(sn.System_N_frst)) =
      (p0_Node.(s.System_N_frst)) &&
      (p0_Node.(sn.System_N_scnd)) =
        ((p0_Node.(s.System_N_frst)).(s.System_N_frst)) &&
      {(some
          (p0_Node.(s.System_N_frst)).(s.System_N_prdc) &&
          (p0_Node.(s.System_N_frst)).(((p0_Node.(s.System_N_frst)).(s.System_N_prdc)).(p0_Node.between)) &&
          (p0_Node.(s.System_N_frst)).(s.System_N_prdc) in
            s.System_members)=>
          (p0_Node.(sn.System_N_status)) = Stabilizing &&
            (p0_Node.(sn.System_N_saved)) =
              ((p0_Node.(s.System_N_frst)).(s.System_N_prdc)) &&
            (all n: Node - p0_Node | (n.(sn.System_N_status)) =
                                       (n.(s.System_N_status))) &&
            (all n: Node - p0_Node | (n.(sn.System_N_saved)) =
                                       (n.(s.System_N_saved)))
        else
          ({(p0_Node !in
               (p0_Node.(s.System_N_frst)).(s.System_N_prdc))=>
               ((p0_Node.(s.System_N_frst)).(sn.System_N_status)) =
                 Rectifying &&
                 ((p0_Node.(s.System_N_frst)).(sn.System_N_saved)) =
                   p0_Node &&
                 (all n: Node - (p0_Node.(s.System_N_frst)) | (n.(sn.System_N_status)) =
                                                                (n.(s.System_N_status))) &&
                 (all n: Node - (p0_Node.(s.System_N_frst)) | (n.(sn.System_N_saved)) =
                                                                (n.(s.System_N_saved)))
             else
               (all n: Node | (n.(sn.System_N_status)) =
                                (n.(s.System_N_status))) &&
                 (all n: Node | (n.(sn.System_N_saved)) =
                                  (n.(s.System_N_saved)))}
           )}
      }

  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Node -> System_N_Live_StabilizeFromSucc)
  (all Node_aa: Node - p0_Node | (Node_aa.(s.System_N_frst)) =
                                 (Node_aa.(sn.System_N_frst)))
  (all Node_aa: Node - p0_Node | (Node_aa.(s.System_N_scnd)) =
                                 (Node_aa.(sn.System_N_scnd)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_prdc)) =
           (Node_aa.(sn.System_N_prdc)))
  (s.System_members) = (sn.System_members)
  {((p0_Node -> System_N).(none.(p0_Node.(sn.(s._nextIsStable)))))=>
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
                   (p0_Node -> System_NScope)))}
       )}

}

pred System_N_Live_StabilizeFromSucc_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some ((p0_Node -> System_N_Live) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_Node -> System_N) in sc1) ||
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
  p0_Node in s.System_members &&
  (p0_Node.(s.System_N_status)) = Rectifying
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_Node -> System_NScope) in (s.dsh_sc_used1))
}


pred System_N_Live_Rectify_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) - (p0_Node -> System_N_Live)) +
     (p0_Node -> System_N_Live))
  {({ p0_Node.((p0_Node.(s.System_N_saved)).((p0_Node.(s.System_N_prdc)).between)) ||
      p0_Node.(s.System_N_prdc) !in s.System_members ||
      no
      p0_Node.(s.System_N_prdc) })=>
    (p0_Node.(sn.System_N_prdc)) =
      (p0_Node.(s.System_N_saved))
  else
    (p0_Node.(sn.System_N_prdc)) =
      (p0_Node.(s.System_N_prdc))}

  (sn.dsh_taken0) = none
  (sn.dsh_taken1) = (p0_Node -> System_N_Live_Rectify)
  (all Node_aa: Node - p0_Node | (Node_aa.(s.System_N_prdc)) =
                                 (Node_aa.(sn.System_N_prdc)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_status)) =
           (Node_aa.(sn.System_N_status)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_saved)) =
           (Node_aa.(sn.System_N_saved)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_frst)) =
           (Node_aa.(sn.System_N_frst)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_scnd)) =
           (Node_aa.(sn.System_N_scnd)))
  (s.System_members) = (sn.System_members)
  {((p0_Node -> System_N).(none.(p0_Node.(sn.(s._nextIsStable)))))=>
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
                   (p0_Node -> System_NScope)))}
       )}

}

pred System_N_Live_Rectify_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some ((p0_Node -> System_N_Live) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_Node -> System_N) in sc1) ||
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
  !(SystemScope in (s.dsh_sc_used0))
  !((p0_Node -> System_NScope) in (s.dsh_sc_used1))
}


pred System_N_Failed_Join_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_Node -> System_N_Live) +
         (p0_Node -> System_N_Failed))) +
     (p0_Node -> System_N_Live))
  (sn.System_members) = ((s.System_members) + p0_Node)
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) = (p0_Node -> System_N_Failed_Join)
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_status)) =
           (Node_aa.(sn.System_N_status)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_saved)) =
           (Node_aa.(sn.System_N_saved)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_frst)) =
           (Node_aa.(sn.System_N_frst)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_scnd)) =
           (Node_aa.(sn.System_N_scnd)))
  (all Node_aa: one
  Node | (Node_aa.(s.System_N_prdc)) =
           (Node_aa.(sn.System_N_prdc)))
  {((p0_Node -> System_N).(none.(p0_Node.(sn.(s._nextIsStable)))))=>
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
                   (p0_Node -> System_NScope)))}
       )}

}

pred System_N_Failed_Join_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  some ((p0_Node -> System_N_Failed) & (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(System in sc0) &&
    !((p0_Node -> System_N) in sc1) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred System_N_Failed_Join [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node] {
  p0_Node.(s.System_N_Failed_Join_pre)
  p0_Node.(sn.(s.System_N_Failed_Join_post))
}

pred _nextIsStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Node: one Node,
	sc0: DshStates,
	sc1: DshIds -> DshStates] {
  !(sc1.(sc0.(p0_Node.(sn.(s.System_N_Live_StabilizeFromPrdc_enabledAfterStep)))))
  !(sc1.(sc0.(p0_Node.(sn.(s.System_N_Live_Flush_enabledAfterStep)))))
  !(sc1.(sc0.(p0_Node.(sn.(s.System_N_Live_Fail_enabledAfterStep)))))
  !(sc1.(sc0.(p0_Node.(sn.(s.System_N_Live_StabilizeFromSucc_enabledAfterStep)))))
  !(sc1.(sc0.(p0_Node.(sn.(s.System_N_Live_Rectify_enabledAfterStep)))))
  !(sc1.(sc0.(p0_Node.(sn.(s.System_N_Failed_Join_enabledAfterStep)))))
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
  (sn.System_N_frst) = (s.System_N_frst)
  (sn.System_N_scnd) = (s.System_N_scnd)
  (sn.System_N_prdc) = (s.System_N_prdc)
  (sn.System_N_status) = (s.System_N_status)
  (sn.System_N_saved) = (s.System_N_saved)
  (sn.System_members) = (s.System_members)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { (some p0_Node: one
      Node | { p0_Node.(sn.(s.System_N_Live_StabilizeFromPrdc)) ||
                 p0_Node.(sn.(s.System_N_Live_Flush)) ||
                 p0_Node.(sn.(s.System_N_Live_Fail)) ||
                 p0_Node.(sn.(s.System_N_Live_StabilizeFromSucc)) ||
                 p0_Node.(sn.(s.System_N_Live_Rectify)) ||
                 p0_Node.(sn.(s.System_N_Failed_Join)) }) ||
    !((some p0_Node: one
         Node | { p0_Node.(s.System_N_Live_StabilizeFromPrdc_pre) ||
                    p0_Node.(s.System_N_Live_Flush_pre) ||
                    p0_Node.(s.System_N_Live_Fail_pre) ||
                    p0_Node.(s.System_N_Live_StabilizeFromSucc_pre) ||
                    p0_Node.(s.System_N_Live_Rectify_pre) ||
                    p0_Node.(s.System_N_Failed_Join_pre) })) &&
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


