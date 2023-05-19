/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-05-18 09:59:29
*/

open util/ring[Identifier] as P0

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot
open util/buffer[bufIdx0, Identifier] as token
abstract sig DshStates {}
abstract sig System extends DshStates {} 
abstract sig System_Process extends System {} 
one sig System_Process_Electing extends System_Process {} 
one sig System_Process_Elected extends System_Process {} 

abstract sig DshIds {}
sig Identifier extends DshIds {} 

sig bufIdx0 {}
sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_sc_used1: DshIds -> DshStates,
  dsh_conf1: DshIds -> DshStates,
  dsh_stable: one boolean/Bool,
  System_elected: set Identifier,
  System_Process_succ: Identifier -> one Identifier,
  System_Process_token: Identifier -> (bufIdx0 -> Identifier)
}

pred dsh_initial [s: one DshSnapshot, pIdentifier: one Identifier] {
  (all pIdentifier: one
  Identifier | one
                 (pIdentifier . (s . System_Process_token)) and
                 (((pIdentifier.nextRing) .
                     (s . System_Process_token)).firstElem)
                   = pIdentifier and
                 no
                 (s . System_elected))
}

pred System_Process_Electing_ConsumeToken_pre [s: one DshSnapshot, pIdentifier: one Identifier] {
  some
((pIdentifier -> System_Process_Electing) & (s . dsh_conf1))
  no
  (s . System_elected) and
  some
  ((pIdentifier . (s . System_Process_token)).elems) and
  ((pIdentifier . (s . System_Process_token)).firstElem).(pIdentifier.gt)
  ! (System in (s . dsh_sc_used0))
  ! ((pIdentifier -> System_Process) in (s . dsh_sc_used1))
}


pred System_Process_Electing_ConsumeToken_post [s: one DshSnapshot, sn: one DshSnapshot, pIdentifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pIdentifier -> System_Process_Electing)) +
     (pIdentifier -> System_Process_Electing))
  (pIdentifier . (s . System_Process_token)).removeFirst
  ((pIdentifier -> System_Process) .
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

pred System_Process_Electing_ConsumeToken_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pIdentifier: one Identifier, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pIdentifier -> System_Process_Electing) & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (System in dsh_scp0) and
    !
    ((pIdentifier -> System_Process) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred System_Process_Electing_ConsumeToken [s: one DshSnapshot, sn: one DshSnapshot, pIdentifier: one Identifier] {
  pIdentifier . (s . System_Process_Electing_ConsumeToken_pre)
  pIdentifier .
  (sn . (s . System_Process_Electing_ConsumeToken_post))
}

pred System_Process_Electing_PassToken_pre [s: one DshSnapshot, pIdentifier: one Identifier] {
  some
((pIdentifier -> System_Process_Electing) & (s . dsh_conf1))
  no
  (s . System_elected) and
  some
  ((pIdentifier . (s . System_Process_token)).elems) and
  ((pIdentifier . (s . System_Process_token)).firstElem).(this.lt)
  ! (System in (s . dsh_sc_used0))
  ! ((pIdentifier -> System_Process) in (s . dsh_sc_used1))
}


pred System_Process_Electing_PassToken_post [s: one DshSnapshot, sn: one DshSnapshot, pIdentifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pIdentifier -> System_Process_Electing)) +
     (pIdentifier -> System_Process_Electing))
  ((pIdentifier . (s . System_Process_token)).firstElem).(((pIdentifier.nextRing)
                                                           .
                                                           (s
                                                              .
                                                              System_Process_token)).addFirst) and
  (all others: Identifier - (pIdentifier.nextRing) | (others
                                                        .
                                                        (sn
                                                           .
                                                           System_Process_token))
                                                       =
                                                       (others
                                                          .
                                                          (s
                                                             .
                                                             System_Process_token)))
  ((pIdentifier -> System_Process) .
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

pred System_Process_Electing_PassToken_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pIdentifier: one Identifier, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pIdentifier -> System_Process_Electing) & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (System in dsh_scp0) and
    !
    ((pIdentifier -> System_Process) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred System_Process_Electing_PassToken [s: one DshSnapshot, sn: one DshSnapshot, pIdentifier: one Identifier] {
  pIdentifier . (s . System_Process_Electing_PassToken_pre)
  pIdentifier .
  (sn . (s . System_Process_Electing_PassToken_post))
}

pred System_Process_Electing_ElectLeader_pre [s: one DshSnapshot, pIdentifier: one Identifier] {
  some
((pIdentifier -> System_Process_Electing) & (s . dsh_conf1))
  no
  (s . System_elected) and
  ((pIdentifier . (s . System_Process_token)).firstElem) =
    pIdentifier
  ! (System in (s . dsh_sc_used0))
  ! ((pIdentifier -> System_Process) in (s . dsh_sc_used1))
}


pred System_Process_Electing_ElectLeader_post [s: one DshSnapshot, sn: one DshSnapshot, pIdentifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (pIdentifier -> System_Process_Elected)) +
     (pIdentifier -> System_Process_Elected))
  (sn . System_elected) = pIdentifier
  ((pIdentifier -> System_Process) .
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

pred System_Process_Electing_ElectLeader_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, pIdentifier: one Identifier, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  some
((pIdentifier -> System_Process_Electing) & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (System in dsh_scp0) and
    !
    ((pIdentifier -> System_Process) in dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred System_Process_Electing_ElectLeader [s: one DshSnapshot, sn: one DshSnapshot, pIdentifier: one Identifier] {
  pIdentifier . (s . System_Process_Electing_ElectLeader_pre)
  pIdentifier .
  (sn . (s . System_Process_Electing_ElectLeader_post))
}

pred _testIfNextStable [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_scp1: DshIds -> DshStates] {
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            System_Process_Electing_ConsumeToken_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            System_Process_Electing_PassToken_enabledAfterStep))))
  !
(dsh_scp1 .
   (dsh_scp0 .
      (sn .
         (s .
            System_Process_Electing_ElectLeader_enabledAfterStep))))
}

pred dsh_small_step [s: one DshSnapshot, sn: one DshSnapshot] {
  (some pIdentifier: one
  Identifier | { pIdentifier .
                   (sn .
                      (s .
                         System_Process_Electing_ConsumeToken)) or
                   pIdentifier .
                     (sn .
                        (s .
                           System_Process_Electing_PassToken)) or
                   pIdentifier .
                     (sn .
                        (s .
                           System_Process_Electing_ElectLeader)) })
}

fact dsh_traces_fact {  DshSnapshot/first . dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s . DshSnapshot/next)
                                       .
                                       (s . dsh_small_step))
}





