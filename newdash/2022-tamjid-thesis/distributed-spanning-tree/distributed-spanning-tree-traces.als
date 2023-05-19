/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-05-18 09:59:26
*/

open util/ordering[Level] as nodeLevel

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

sig Level {}

abstract sig DshStates {}
abstract sig DistrubedTreeSpanning extends DshStates {} 
abstract sig DistrubedTreeSpanning_N extends DistrubedTreeSpanning {} 
one sig DistrubedTreeSpanning_N_Unassigned extends DistrubedTreeSpanning_N {} 
one sig DistrubedTreeSpanning_N_Assigned extends DistrubedTreeSpanning_N {} 

abstract sig DshIds {}
sig Node extends DshIds {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_sc_used1: DshIds -> DshStates,
  dsh_conf1: DshIds -> DshStates,
  dsh_stable: one boolean/Bool,
  DistrubedTreeSpanning_N_level: Node -> lone Level,
  DistrubedTreeSpanning_N_message: Node -> (Node -> Level),
  DistrubedTreeSpanning_root: one Node,
  DistrubedTreeSpanning_N_parent: Node -> lone Node
}

pred dsh_initial [s: one DshSnapshot, pNode: one Node] {
  (all pNode: one
  Node | no
           (pNode . (s . DistrubedTreeSpanning_N_level)) and
           no
           (pNode . (s . DistrubedTreeSpanning_N_parent)) and
           no
           (pNode . (s . DistrubedTreeSpanning_N_message)))
}

pred DistrubedTreeSpanning_N_Assigned_sendMessage_pre [s: one DshSnapshot, pNode: one Node] {
  some
((pNode -> DistrubedTreeSpanning_N_Assigned) &
   (s . dsh_conf1))
  (some n: Node | no (n . (s . DistrubedTreeSpanning_N_level)))
  ! (DistrubedTreeSpanning in (s . dsh_sc_used0))
  ! ((pNode -> DistrubedTreeSpanning_N) in (s . dsh_sc_used1))
}


pred DistrubedTreeSpanning_N_Assigned_sendMessage_post [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pNode -> DistrubedTreeSpanning_N_Assigned)) +
     (pNode -> DistrubedTreeSpanning_N_Assigned))
  (some n: Node - pNode | no
                          (n .
                             (s .
                                DistrubedTreeSpanning_N_message)) and
                          (n .
                             (sn .
                                DistrubedTreeSpanning_N_message))
                            =
                            (pNode ->
                               (pNode .
                                  (s .
                                     DistrubedTreeSpanning_N_level))) and
                          (all others: Node - n | (others .
                                                     (sn .
                                                        DistrubedTreeSpanning_N_message))
                                                    =
                                                    (others
                                                       .
                                                       (s .
                                                          DistrubedTreeSpanning_N_message))))
  ((pNode -> DistrubedTreeSpanning_N) .
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

pred DistrubedTreeSpanning_N_Assigned_sendMessage_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pNode -> DistrubedTreeSpanning_N_Assigned) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (DistrubedTreeSpanning in dsh_scp0) and
    !
    ((pNode -> DistrubedTreeSpanning_N) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred DistrubedTreeSpanning_N_Assigned_sendMessage [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  pNode .
  (s . DistrubedTreeSpanning_N_Assigned_sendMessage_pre)
  pNode .
  (sn .
     (s . DistrubedTreeSpanning_N_Assigned_sendMessage_post))
}

pred DistrubedTreeSpanning_N_Unassigned_RootAssign_pre [s: one DshSnapshot, pNode: one Node] {
  some
((pNode -> DistrubedTreeSpanning_N_Unassigned) &
   (s . dsh_conf1))
  pNode in (s . DistrubedTreeSpanning_root)
  ! (DistrubedTreeSpanning in (s . dsh_sc_used0))
  ! ((pNode -> DistrubedTreeSpanning_N) in (s . dsh_sc_used1))
}


pred DistrubedTreeSpanning_N_Unassigned_RootAssign_post [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pNode -> DistrubedTreeSpanning_N_Assigned)) +
     (pNode -> DistrubedTreeSpanning_N_Assigned))
  (pNode . (sn . DistrubedTreeSpanning_N_level)) =
  nodeLevel/first and
  (pNode . (sn . DistrubedTreeSpanning_N_parent)) = pNode
  ((pNode -> DistrubedTreeSpanning_N) .
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

pred DistrubedTreeSpanning_N_Unassigned_RootAssign_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pNode -> DistrubedTreeSpanning_N_Unassigned) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (DistrubedTreeSpanning in dsh_scp0) and
    !
    ((pNode -> DistrubedTreeSpanning_N) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred DistrubedTreeSpanning_N_Unassigned_RootAssign [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  pNode .
  (s . DistrubedTreeSpanning_N_Unassigned_RootAssign_pre)
  pNode .
  (sn .
     (s . DistrubedTreeSpanning_N_Unassigned_RootAssign_post))
}

pred DistrubedTreeSpanning_N_Unassigned_NodeAssign_pre [s: one DshSnapshot, pNode: one Node] {
  some
((pNode -> DistrubedTreeSpanning_N_Unassigned) &
   (s . dsh_conf1))
  some (pNode . (s . DistrubedTreeSpanning_N_message))
  ! (DistrubedTreeSpanning in (s . dsh_sc_used0))
  ! ((pNode -> DistrubedTreeSpanning_N) in (s . dsh_sc_used1))
}


pred DistrubedTreeSpanning_N_Unassigned_NodeAssign_post [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pNode -> DistrubedTreeSpanning_N_Assigned)) +
     (pNode -> DistrubedTreeSpanning_N_Assigned))
  (pNode . (sn . DistrubedTreeSpanning_N_level)) =
  ((Node.(pNode . (s . DistrubedTreeSpanning_N_message))).nodeLevel/next) and
  (pNode . (sn . DistrubedTreeSpanning_N_parent)) =
    ((pNode . (s . DistrubedTreeSpanning_N_message)).Level)
  ((pNode -> DistrubedTreeSpanning_N) .
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

pred DistrubedTreeSpanning_N_Unassigned_NodeAssign_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pNode -> DistrubedTreeSpanning_N_Unassigned) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (DistrubedTreeSpanning in dsh_scp0) and
    !
    ((pNode -> DistrubedTreeSpanning_N) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred DistrubedTreeSpanning_N_Unassigned_NodeAssign [s: one DshSnapshot, sn: one DshSnapshot, pNode: one Node] {
  pNode .
  (s . DistrubedTreeSpanning_N_Unassigned_NodeAssign_pre)
  pNode .
  (sn .
     (s . DistrubedTreeSpanning_N_Unassigned_NodeAssign_post))
}

pred _testIfNextStable [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            DistrubedTreeSpanning_N_Assigned_sendMessage_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            DistrubedTreeSpanning_N_Unassigned_RootAssign_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            DistrubedTreeSpanning_N_Unassigned_NodeAssign_enabledAfterStep))))
}

pred dsh_small_step [s: one DshSnapshot, sn: one DshSnapshot] {
  (some pNode: one
  Node | { pNode .
             (sn .
                (s .
                   DistrubedTreeSpanning_N_Assigned_sendMessage)) or
             pNode .
               (sn .
                  (s .
                     DistrubedTreeSpanning_N_Unassigned_RootAssign)) or
             pNode .
               (sn .
                  (s .
                     DistrubedTreeSpanning_N_Unassigned_NodeAssign)) })
}

fact dsh_traces_fact {  DshSnapshot/first . dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s . DshSnapshot/next)
                                       .
                                       (s . dsh_small_step))
}

