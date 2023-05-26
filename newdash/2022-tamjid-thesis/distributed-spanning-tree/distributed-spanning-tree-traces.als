/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-05-26 13:58:12
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

pred dsh_initial [s: one DshSnapshot, p0_Node: one Node] {
  (all p0_Node: one
  Node | (s . dsh_conf0) = none and
           (s . dsh_conf1) =
             (Node -> DistrubedTreeSpanning_N_Unassigned) and
           (s . dsh_sc_used1) = none and
           (s . dsh_events1) in DshEnvEvents and
           no
           (p0_Node . (s . DistrubedTreeSpanning_N_level)) and
           no
           (p0_Node . (s . DistrubedTreeSpanning_N_parent)) and
           no
           (p0_Node . (s . DistrubedTreeSpanning_N_message)))
  (s . dsh_stable) = boolean/True
}

pred DistrubedTreeSpanning_N_Assigned_sendMessage_pre [s: one DshSnapshot, p0_Node: one Node] {
  some
((p0_Node -> DistrubedTreeSpanning_N_Assigned) &
   (s . dsh_conf1))
  (some n: Node | no (n . (s . DistrubedTreeSpanning_N_level)))
  ! (DistrubedTreeSpanning in (s . dsh_sc_used0))
  !
((p0_Node -> DistrubedTreeSpanning_N) in (s . dsh_sc_used1))
}


pred DistrubedTreeSpanning_N_Assigned_sendMessage_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Node: one Node] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (p0_Node -> DistrubedTreeSpanning_N_Assigned)) +
     (p0_Node -> DistrubedTreeSpanning_N_Assigned))
  (some n: Node - thisNode | no
                             (n .
                                (s .
                                   DistrubedTreeSpanning_N_message)) and
                             (n .
                                (sn .
                                   DistrubedTreeSpanning_N_message))
                               =
                               (thisNode ->
                                  (p0_Node .
                                     (s .
                                        DistrubedTreeSpanning_N_level))) and
                             (all others: Node - n | (others
                                                        .
                                                        (sn
                                                           .
                                                           DistrubedTreeSpanning_N_message))
                                                       =
                                                       (others
                                                          .
                                                          (s
                                                             .
                                                             DistrubedTreeSpanning_N_message))))
  ((p0_Node -> DistrubedTreeSpanning_N) .
   (none . (p0_Node . (sn . (s . _testIfNextStable)))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           ((sn . dsh_sc_used0) = none and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Node -> DistrubedTreeSpanning_N)))
       )

}

pred DistrubedTreeSpanning_N_Assigned_sendMessage_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Node: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((p0_Node -> DistrubedTreeSpanning_N_Assigned) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (DistrubedTreeSpanning in dsh_scp0) and
    !
    ((p0_Node -> DistrubedTreeSpanning_N) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred DistrubedTreeSpanning_N_Assigned_sendMessage [s: one DshSnapshot, sn: one DshSnapshot, p0_Node: one Node] {
  p0_Node .
  (s . DistrubedTreeSpanning_N_Assigned_sendMessage_pre)
  p0_Node .
  (sn .
     (s . DistrubedTreeSpanning_N_Assigned_sendMessage_post))
}

pred DistrubedTreeSpanning_N_Unassigned_RootAssign_pre [s: one DshSnapshot, p0_Node: one Node] {
  some
((p0_Node -> DistrubedTreeSpanning_N_Unassigned) &
   (s . dsh_conf1))
  thisNode in (s . DistrubedTreeSpanning_root)
  ! (DistrubedTreeSpanning in (s . dsh_sc_used0))
  !
((p0_Node -> DistrubedTreeSpanning_N) in (s . dsh_sc_used1))
}


pred DistrubedTreeSpanning_N_Unassigned_RootAssign_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Node: one Node] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  ((((s . dsh_conf1) -
       (p0_Node -> DistrubedTreeSpanning_N_Unassigned)) -
      (p0_Node -> DistrubedTreeSpanning_N_Assigned)) +
     (p0_Node -> DistrubedTreeSpanning_N_Assigned))
  (p0_Node . (sn . DistrubedTreeSpanning_N_level)) =
  nodeLevel/first and
  (p0_Node . (sn . DistrubedTreeSpanning_N_parent)) =
    thisNode
  ((p0_Node -> DistrubedTreeSpanning_N) .
   (none . (p0_Node . (sn . (s . _testIfNextStable)))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           ((sn . dsh_sc_used0) = none and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Node -> DistrubedTreeSpanning_N)))
       )

}

pred DistrubedTreeSpanning_N_Unassigned_RootAssign_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Node: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((p0_Node -> DistrubedTreeSpanning_N_Unassigned) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (DistrubedTreeSpanning in dsh_scp0) and
    !
    ((p0_Node -> DistrubedTreeSpanning_N) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred DistrubedTreeSpanning_N_Unassigned_RootAssign [s: one DshSnapshot, sn: one DshSnapshot, p0_Node: one Node] {
  p0_Node .
  (s . DistrubedTreeSpanning_N_Unassigned_RootAssign_pre)
  p0_Node .
  (sn .
     (s . DistrubedTreeSpanning_N_Unassigned_RootAssign_post))
}

pred DistrubedTreeSpanning_N_Unassigned_NodeAssign_pre [s: one DshSnapshot, p0_Node: one Node] {
  some
((p0_Node -> DistrubedTreeSpanning_N_Unassigned) &
   (s . dsh_conf1))
  some (p0_Node . (s . DistrubedTreeSpanning_N_message))
  ! (DistrubedTreeSpanning in (s . dsh_sc_used0))
  !
((p0_Node -> DistrubedTreeSpanning_N) in (s . dsh_sc_used1))
}


pred DistrubedTreeSpanning_N_Unassigned_NodeAssign_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Node: one Node] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  ((((s . dsh_conf1) -
       (p0_Node -> DistrubedTreeSpanning_N_Unassigned)) -
      (p0_Node -> DistrubedTreeSpanning_N_Assigned)) +
     (p0_Node -> DistrubedTreeSpanning_N_Assigned))
  (p0_Node . (sn . DistrubedTreeSpanning_N_level)) =
  ((Node.(p0_Node . (s . DistrubedTreeSpanning_N_message))).nodeLevel/next) and
  (p0_Node . (sn . DistrubedTreeSpanning_N_parent)) =
    ((p0_Node . (s . DistrubedTreeSpanning_N_message)).Level)
  ((p0_Node -> DistrubedTreeSpanning_N) .
   (none . (p0_Node . (sn . (s . _testIfNextStable)))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       { (s . dsh_stable) = boolean/True or
           !
           ((s . dsh_stable) = boolean/True) })
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           ((sn . dsh_sc_used0) = none and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Node -> DistrubedTreeSpanning_N)))
       )

}

pred DistrubedTreeSpanning_N_Unassigned_NodeAssign_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Node: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((p0_Node -> DistrubedTreeSpanning_N_Unassigned) &
   (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (DistrubedTreeSpanning in dsh_scp0) and
    !
    ((p0_Node -> DistrubedTreeSpanning_N) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred DistrubedTreeSpanning_N_Unassigned_NodeAssign [s: one DshSnapshot, sn: one DshSnapshot, p0_Node: one Node] {
  p0_Node .
  (s . DistrubedTreeSpanning_N_Unassigned_NodeAssign_pre)
  p0_Node .
  (sn .
     (s . DistrubedTreeSpanning_N_Unassigned_NodeAssign_post))
}

pred _testIfNextStable [s: one DshSnapshot, sn: one DshSnapshot, p0_Node: one Node, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
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
  (some p0_Node: one
  Node | { p0_Node .
             (sn .
                (s .
                   DistrubedTreeSpanning_N_Assigned_sendMessage)) or
             p0_Node .
               (sn .
                  (s .
                     DistrubedTreeSpanning_N_Unassigned_RootAssign)) or
             p0_Node .
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

