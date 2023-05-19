/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-05-18 09:59:25
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
  System_N_status: Node -> Status,
  System_N_saved: Node -> lone Node,
  System_N_frst: Node -> lone Node,
  System_N_scnd: Node -> lone Node,
  System_N_prdc: Node -> lone Node,
  System_members: Node
}

pred dsh_initial [s: one DshSnapshot, pNode: one Node] {
  (all pNode: one
  Node | no
           (pNode . (s . System_N_status)) and
           no
           (pNode . (s . System_N_saved)) and
           (pNode . (s . System_N_frst)) = (pNode.nextNode) and
           (pNode . (s . System_N_scnd)) =
             ((pNode . (s . System_N_frst)).nextNode) and
           (pNode . (s . System_N_prdc)) = (pNode.prevNode) and
           Node in (s . System_members))
}

pred System_N_Live_StabilizeFromPrdc_pre [s: one DshSnapshot, pNode: one Node] {
  some ((pNode -> System_N_Live) & (s . dsh_conf1))
  pNode in (s . System_members) and
  (pNode . (s . System_N_status)) = Stabilizing and
  (pNode . (s . System_N_frst)).((pNode .
                                    (s . System_N_saved)).(pNode.between))
  ! (System in (s . dsh_sc_used0))
  ! ((pNode -> System_N) in (s . dsh_sc_used1))
}


pred System_N_Live_StabilizeFromPrdc_post [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) - (pNode -> System_N_Live)) +
     (pNode -> System_N_Live))
  no
  (pNode . (sn . System_N_status)) and
  no
  (pNode . (sn . System_N_saved)) and
  ((pNode . (s . System_N_saved)) !in (s . System_members))=>
      (pNode . (sn . System_N_frst)) =
        (pNode . (s . System_N_frst)) and
        (pNode . (sn . System_N_scnd)) =
          (pNode . (s . System_N_scnd)) and
        (all n: Node - pNode | (n . (sn . System_N_status))
                                 =
                                 (n . (s . System_N_status))) and
        (all n: Node - pNode | (n . (sn . System_N_saved)) =
                                 (n . (s . System_N_saved)))
    else
      (pNode . (sn . System_N_frst)) =
        (pNode . (s . System_N_saved)) and
        (pNode . (sn . System_N_scnd)) =
          ((pNode . (s . System_N_saved)) .
             (s . System_N_frst)) and
        ((pNode . (s . System_N_saved)) .
           (sn . System_N_status)) = Rectifying and
        ((pNode . (s . System_N_saved)) .
           (sn . System_N_saved)) = pNode and
        (all n: (Node - (pNode . (s . System_N_saved))) -
                  pNode | (n . (sn . System_N_status)) =
                            (n . (s . System_N_status))) and
        (all n: (Node - (pNode . (s . System_N_saved))) -
                  pNode | (n . (sn . System_N_saved)) =
                            (n . (s . System_N_saved)))
  
  ((pNode -> System_N) .
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

pred System_N_Live_StabilizeFromPrdc_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some ((pNode -> System_N_Live) & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (System in dsh_scp0) and
    !
    ((pNode -> System_N) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred System_N_Live_StabilizeFromPrdc [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  pNode . (s . System_N_Live_StabilizeFromPrdc_pre)
  pNode . (sn . (s . System_N_Live_StabilizeFromPrdc_post))
}

pred System_N_Live_Flush_pre [s: one DshSnapshot, pNode: one Node] {
  some ((pNode -> System_N_Live) & (s . dsh_conf1))
  pNode in (s . System_members) and
  (pNode . (s . System_N_prdc)) !in (s . System_members)
  ! (System in (s . dsh_sc_used0))
  ! ((pNode -> System_N) in (s . dsh_sc_used1))
}


pred System_N_Live_Flush_post [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) - (pNode -> System_N_Live)) +
     (pNode -> System_N_Live))
  (pNode . (sn . System_N_prdc)) = none
  ((pNode -> System_N) .
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

pred System_N_Live_Flush_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some ((pNode -> System_N_Live) & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (System in dsh_scp0) and
    !
    ((pNode -> System_N) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred System_N_Live_Flush [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  pNode . (s . System_N_Live_Flush_pre)
  pNode . (sn . (s . System_N_Live_Flush_post))
}

pred System_N_Live_Fail_pre [s: one DshSnapshot, pNode: one Node] {
  some ((pNode -> System_N_Live) & (s . dsh_conf1))
  (all n: Node - pNode | some
  (((s . System_members) - pNode) &
     ((n . (s . System_N_frst)) + (n . (s . System_N_scnd)))))
  ! (System in (s . dsh_sc_used0))
  ! ((pNode -> System_N) in (s . dsh_sc_used1))
}


pred System_N_Live_Fail_post [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) - (pNode -> System_N_Failed)) +
     (pNode -> System_N_Failed))
  (sn . System_members) = ((s . System_members) - pNode) and
  (pNode . (sn . System_N_frst)) = none and
  (pNode . (sn . System_N_scnd)) = none and
  (pNode . (sn . System_N_prdc)) = none and
  (pNode . (sn . System_N_status)) = none
  ((pNode -> System_N) .
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

pred System_N_Live_Fail_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some ((pNode -> System_N_Live) & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (System in dsh_scp0) and
    !
    ((pNode -> System_N) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred System_N_Live_Fail [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  pNode . (s . System_N_Live_Fail_pre)
  pNode . (sn . (s . System_N_Live_Fail_post))
}

pred System_N_Live_StabilizeFromSucc_pre [s: one DshSnapshot, pNode: one Node] {
  some ((pNode -> System_N_Live) & (s . dsh_conf1))
  no (pNode . (s . System_N_status))
  ! (System in (s . dsh_sc_used0))
  ! ((pNode -> System_N) in (s . dsh_sc_used1))
}


pred System_N_Live_StabilizeFromSucc_post [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) - (pNode -> System_N_Live)) +
     (pNode -> System_N_Live))
  ((pNode . (s . System_N_frst)) !in (s . System_members))=>
    (pNode . (sn . System_N_frst)) =
      (pNode . (s . System_N_scnd)) and
      (pNode . (sn . System_N_scnd)) =
        ((pNode . (s . System_N_scnd)).nextNode) and
      (all n: Node | (n . (sn . System_N_status)) =
                       (n . (s . System_N_status))) and
      (all n: Node | (n . (sn . System_N_saved)) =
                       (n . (s . System_N_saved)))
  else
    (pNode . (sn . System_N_frst)) =
      (pNode . (s . System_N_frst)) and
      (pNode . (sn . System_N_scnd)) =
        ((pNode . (s . System_N_frst)) . (s . System_N_frst)) and
      (some
         ((pNode . (s . System_N_frst)) .
            (s . System_N_prdc)) and
         (pNode . (s . System_N_frst)).(((pNode .
                                            (s .
                                               System_N_frst))
                                           .
                                           (s .
                                              System_N_prdc)).(pNode.between)) and
         ((pNode . (s . System_N_frst)) .
            (s . System_N_prdc)) in (s . System_members))=>
          (pNode . (sn . System_N_status)) = Stabilizing and
            (pNode . (sn . System_N_saved)) =
              ((pNode . (s . System_N_frst)) .
                 (s . System_N_prdc)) and
            (all n: Node - pNode | (n .
                                      (sn . System_N_status))
                                     =
                                     (n .
                                        (s . System_N_status))) and
            (all n: Node - pNode | (n .
                                      (sn . System_N_saved))
                                     =
                                     (n .
                                        (s . System_N_saved)))
        else
          ((pNode !in
              ((pNode . (s . System_N_frst)) .
                 (s . System_N_prdc)))=>
               ((pNode . (s . System_N_frst)) .
                  (sn . System_N_status)) = Rectifying and
                 ((pNode . (s . System_N_frst)) .
                    (sn . System_N_saved)) = pNode and
                 (all n: Node -
                           (pNode . (s . System_N_frst)) | (n
                                                              .
                                                              (sn
                                                                 .
                                                                 System_N_status))
                                                             =
                                                             (n
                                                                .
                                                                (s
                                                                   .
                                                                   System_N_status))) and
                 (all n: Node -
                           (pNode . (s . System_N_frst)) | (n
                                                              .
                                                              (sn
                                                                 .
                                                                 System_N_saved))
                                                             =
                                                             (n
                                                                .
                                                                (s
                                                                   .
                                                                   System_N_saved)))
             else
               (all n: Node | (n . (sn . System_N_status)) =
                                (n . (s . System_N_status))) and
                 (all n: Node | (n . (sn . System_N_saved))
                                  =
                                  (n . (s . System_N_saved)))
           )
      

  ((pNode -> System_N) .
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

pred System_N_Live_StabilizeFromSucc_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some ((pNode -> System_N_Live) & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (System in dsh_scp0) and
    !
    ((pNode -> System_N) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred System_N_Live_StabilizeFromSucc [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  pNode . (s . System_N_Live_StabilizeFromSucc_pre)
  pNode . (sn . (s . System_N_Live_StabilizeFromSucc_post))
}

pred System_N_Live_Rectify_pre [s: one DshSnapshot, pNode: one Node] {
  some ((pNode -> System_N_Live) & (s . dsh_conf1))
  pNode in (s . System_members) and
  (pNode . (s . System_N_status)) = Rectifying
  ! (System in (s . dsh_sc_used0))
  ! ((pNode -> System_N) in (s . dsh_sc_used1))
}


pred System_N_Live_Rectify_post [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) - (pNode -> System_N_Live)) +
     (pNode -> System_N_Live))
  ({ pNode.((pNode . (s . System_N_saved)).((pNode .
                                             (s .
                                                System_N_prdc)).between)) or
     (pNode . (s . System_N_prdc)) !in (s . System_members) or
     no
     (pNode . (s . System_N_prdc)) })=>
    (pNode . (sn . System_N_prdc)) =
      (pNode . (s . System_N_saved))
  else
    (pNode . (sn . System_N_prdc)) =
      (pNode . (s . System_N_prdc))

  ((pNode -> System_N) .
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

pred System_N_Live_Rectify_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some ((pNode -> System_N_Live) & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (System in dsh_scp0) and
    !
    ((pNode -> System_N) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred System_N_Live_Rectify [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  pNode . (s . System_N_Live_Rectify_pre)
  pNode . (sn . (s . System_N_Live_Rectify_post))
}

pred System_N_Failed_Join_pre [s: one DshSnapshot, pNode: one Node] {
  some ((pNode -> System_N_Failed) & (s . dsh_conf1))
  pNode !in (s . System_members)
  ! (System in (s . dsh_sc_used0))
  ! ((pNode -> System_N) in (s . dsh_sc_used1))
}


pred System_N_Failed_Join_post [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) - (pNode -> System_N_Live)) +
     (pNode -> System_N_Live))
  (sn . System_members) = ((s . System_members) + pNode)
  ((pNode -> System_N) .
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

pred System_N_Failed_Join_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some ((pNode -> System_N_Failed) & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (System in dsh_scp0) and
    !
    ((pNode -> System_N) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred System_N_Failed_Join [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  pNode . (s . System_N_Failed_Join_pre)
  pNode . (sn . (s . System_N_Failed_Join_post))
}

pred _testIfNextStable [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            System_N_Live_StabilizeFromPrdc_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn . (s . System_N_Live_Flush_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn . (s . System_N_Live_Fail_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            System_N_Live_StabilizeFromSucc_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn . (s . System_N_Live_Rectify_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn . (s . System_N_Failed_Join_enabledAfterStep))))
}

pred dsh_small_step [s: one DshSnapshot, sn: one DshSnapshot] {
  (some pNode: one
  Node | { pNode .
             (sn . (s . System_N_Live_StabilizeFromPrdc)) or
             pNode . (sn . (s . System_N_Live_Flush)) or
             pNode . (sn . (s . System_N_Live_Fail)) or
             pNode .
               (sn . (s . System_N_Live_StabilizeFromSucc)) or
             pNode . (sn . (s . System_N_Live_Rectify)) or
             pNode . (sn . (s . System_N_Failed_Join)) })
}

fact dsh_traces_fact {  DshSnapshot/first . dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s . DshSnapshot/next)
                                       .
                                       (s . dsh_small_step))
}


