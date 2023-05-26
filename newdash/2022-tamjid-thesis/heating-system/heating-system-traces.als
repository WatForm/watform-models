/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-05-25 20:50:50
*/

open util/ordering[Temp] as temp

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

sig Temp{}
abstract sig ValvePos {}
one sig OPEN, HALF, CLOSED extends ValvePos {}

abstract sig DshStates {}
abstract sig HeatingSystem extends DshStates {} 
abstract sig HeatingSystem_Functioning extends HeatingSystem {} 
abstract sig HeatingSystem_Functioning_Furnace extends HeatingSystem_Functioning {} 
abstract sig HeatingSystem_Functioning_Furnace_Furnace_Normal extends HeatingSystem_Functioning_Furnace {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off extends HeatingSystem_Functioning_Furnace_Furnace_Normal {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating extends HeatingSystem_Functioning_Furnace_Furnace_Normal {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running extends HeatingSystem_Functioning_Furnace_Furnace_Normal {} 
abstract sig HeatingSystem_Functioning_Controller extends HeatingSystem_Functioning {} 
one sig HeatingSystem_Functioning_Controller_Off extends HeatingSystem_Functioning_Controller {} 
abstract sig HeatingSystem_Functioning_Controller_On extends HeatingSystem_Functioning_Controller {} 
one sig HeatingSystem_Functioning_Controller_On_Idle extends HeatingSystem_Functioning_Controller_On {} 
one sig HeatingSystem_Functioning_Controller_On_Heater_Active extends HeatingSystem_Functioning_Controller_On {} 
abstract sig HeatingSystem_Functioning_Room extends HeatingSystem_Functioning {} 
abstract sig HeatingSystem_Functioning_Room_No_Heat_Request extends HeatingSystem_Functioning_Room {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat extends HeatingSystem_Functioning_Room_No_Heat_Request {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat extends HeatingSystem_Functioning_Room_No_Heat_Request {} 
abstract sig HeatingSystem_Functioning_Room_Heat_Requested extends HeatingSystem_Functioning_Room {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating extends HeatingSystem_Functioning_Room_Heat_Requested {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool extends HeatingSystem_Functioning_Room_Heat_Requested {} 
one sig HeatingSystem_ERROR extends HeatingSystem {} 

abstract sig DshIds {}
sig Identifier extends DshIds {} 

abstract sig DshEvents {}
abstract sig DshIntEvents extends DshEvents {} 
one sig HeatingSystem_furnaceReset extends DshIntEvents {} 
one sig HeatingSystem_furnaceNotRunning extends DshIntEvents {} 
one sig HeatingSystem_deactivate extends DshIntEvents {} 
one sig HeatingSystem_furnaceRunning extends DshIntEvents {} 
one sig HeatingSystem_activate extends DshIntEvents {} 
abstract sig DshEnvEvents extends DshEvents {} 
one sig HeatingSystem_Functioning_Room_waitedForWarmth extends DshEnvEvents {} 
one sig HeatingSystem_Functioning_Room_waitedForCool extends DshEnvEvents {} 
one sig HeatingSystem_TurnOn extends DshEnvEvents {} 
one sig HeatingSystem_furnaceFault extends DshEnvEvents {} 
one sig HeatingSystem_heatSwitchOn extends DshEnvEvents {} 
one sig HeatingSystem_Reset extends DshEnvEvents {} 
one sig HeatingSystem_userReset extends DshEnvEvents {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_events0: set DshEvents,
  dsh_sc_used1: DshIds -> DshStates,
  dsh_conf1: DshIds -> DshStates,
  dsh_events1: DshIds -> DshEvents,
  dsh_stable: one boolean/Bool,
  HeatingSystem_Functioning_Room_requestHeat: Identifier ->
                                              one Bool,
  HeatingSystem_Functioning_Room_actualTemp: Identifier -> one
                                             Temp,
  HeatingSystem_Functioning_Controller_controllerOn: one Bool,
  HeatingSystem_Functioning_Room_desiredTemp: Identifier ->
                                              one Temp,
  HeatingSystem_Functioning_Room_valvePos: Identifier -> one
                                           ValvePos
}

pred dsh_initial [s: one DshSnapshot, p0_Identifier: one Identifier] {
  (all p0_Identifier: one
  Identifier | (s . dsh_conf0) =
                 (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off
                    +
                    HeatingSystem_Functioning_Controller_Off) and
                 (s . dsh_conf1) =
                   (Identifier ->
                      HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) and
                 (s . dsh_sc_used1) = none and
                 (s . dsh_events1) in DshEnvEvents and
                 (s .
                    HeatingSystem_Functioning_Controller_controllerOn)
                   = False and
                 (p0_Identifier .
                    (s .
                       HeatingSystem_Functioning_Room_requestHeat))
                   = False and
                 (p0_Identifier .
                    (s .
                       HeatingSystem_Functioning_Room_valvePos))
                   = CLOSED)
}

pred HeatingSystem_Functioning_Controller_Off_T8_pre [s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Controller_Off & (s . dsh_conf0))
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
(HeatingSystem_Functioning_Controller in (s . dsh_sc_used0))
  ((s . dsh_stable) = boolean/True)=>
    (HeatingSystem_heatSwitchOn in
       ((s . dsh_events0) :> DshEnvEvents))
  else
    (HeatingSystem_heatSwitchOn in (s . dsh_events0))

}


pred HeatingSystem_Functioning_Controller_Off_T8_post [s: one DshSnapshot, sn: one DshSnapshot] {
  (sn . dsh_conf0) =
  (((((s . dsh_conf0) -
        HeatingSystem_Functioning_Controller_Off) -
       HeatingSystem_Functioning_Controller_On_Idle) -
      HeatingSystem_Functioning_Controller_On_Heater_Active)
     + HeatingSystem_Functioning_Controller_On_Idle)
  (sn . dsh_conf1) = (s . dsh_conf1)
  (sn . HeatingSystem_Functioning_Controller_controllerOn) =
  True
  ((none -> none) .
   (none .
      (HeatingSystem_furnaceReset .
         (HeatingSystem_Functioning_Controller .
            (none . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) =
              HeatingSystem_furnaceReset and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              (HeatingSystem_furnaceReset +
                 ((s . dsh_events0) :> DshIntEvents)) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) =
              HeatingSystem_furnaceReset and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_events0) =
              ((s . dsh_events0) +
                 HeatingSystem_furnaceReset) and
              (sn . dsh_sc_used0) =
                ((s . dsh_sc_used0) +
                   HeatingSystem_Functioning_Controller) and
              (sn . dsh_sc_used1) = (s . dsh_sc_used1))
       )

}

pred HeatingSystem_Functioning_Controller_Off_T8_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Controller_Off & (sn . dsh_conf0))
  ((s . dsh_stable) = boolean/True)=>
    (!
       (HeatingSystem in dsh_scp0) and
       !
       (HeatingSystem_Functioning_Controller in dsh_scp0) and
       HeatingSystem_heatSwitchOn in
         (((s . dsh_events0) & DshEnvEvents) + dsh_genEvs0))
  else
    (HeatingSystem_heatSwitchOn in
       ((s . dsh_events0) + dsh_genEvs0))

}

pred HeatingSystem_Functioning_Controller_Off_T8 [s: one DshSnapshot, sn: one DshSnapshot] {
  s . HeatingSystem_Functioning_Controller_Off_T8_pre
  sn . (s . HeatingSystem_Functioning_Controller_Off_T8_post)
}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T10_pre [s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Controller_On_Heater_Active &
   (s . dsh_conf0))
  (no r: Identifier | (r .
                       (s .
                          HeatingSystem_Functioning_Room_requestHeat))
                      = True)
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
(HeatingSystem_Functioning_Controller in (s . dsh_sc_used0))
}


pred HeatingSystem_Functioning_Controller_On_Heater_Active_T10_post [s: one DshSnapshot, sn: one DshSnapshot] {
  (sn . dsh_conf0) =
  ((((s . dsh_conf0) -
       HeatingSystem_Functioning_Controller_On_Idle) -
      HeatingSystem_Functioning_Controller_On_Heater_Active)
     + HeatingSystem_Functioning_Controller_On_Idle)
  (sn . dsh_conf1) = (s . dsh_conf1)
  ((none -> none) .
   (none .
      (HeatingSystem_deactivate .
         (HeatingSystem_Functioning_Controller .
            (none . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) =
              HeatingSystem_deactivate and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              (HeatingSystem_deactivate +
                 ((s . dsh_events0) :> DshIntEvents)) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) =
              HeatingSystem_deactivate and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_events0) =
              ((s . dsh_events0) + HeatingSystem_deactivate) and
              (sn . dsh_sc_used0) =
                ((s . dsh_sc_used0) +
                   HeatingSystem_Functioning_Controller) and
              (sn . dsh_sc_used1) = (s . dsh_sc_used1))
       )

}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T10_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Controller_On_Heater_Active &
   (sn . dsh_conf0))
  { (s . dsh_stable) = boolean/True and
    !
    (HeatingSystem in dsh_scp0) and
    !
    (HeatingSystem_Functioning_Controller in dsh_scp0) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T10 [s: one DshSnapshot, sn: one DshSnapshot] {
  s .
  HeatingSystem_Functioning_Controller_On_Heater_Active_T10_pre
  sn .
  (s .
     HeatingSystem_Functioning_Controller_On_Heater_Active_T10_post)
}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T11_pre [s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Controller_On_Heater_Active &
   (s . dsh_conf0))
  ! (HeatingSystem in (s . dsh_sc_used0))
  ((s . dsh_stable) = boolean/True)=>
    (HeatingSystem_furnaceFault in
       ((s . dsh_events0) :> DshEnvEvents))
  else
    (HeatingSystem_furnaceFault in (s . dsh_events0))

}


pred HeatingSystem_Functioning_Controller_On_Heater_Active_T11_post [s: one DshSnapshot, sn: one DshSnapshot] {
  (sn . dsh_conf0) =
  (((((((((s . dsh_conf0) -
            HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off)
           -
           HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating)
          -
          HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)
         - HeatingSystem_Functioning_Controller_Off) -
        HeatingSystem_Functioning_Controller_On_Idle) -
       HeatingSystem_Functioning_Controller_On_Heater_Active)
      - HeatingSystem_ERROR) + HeatingSystem_ERROR)
  (sn . dsh_conf1) =
  (((((s . dsh_conf1) -
        (Identifier ->
           HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
       -
       (Identifier ->
          HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))
      -
      (Identifier ->
         HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
     -
     (Identifier ->
        HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))
  (sn . HeatingSystem_Functioning_Controller_controllerOn) =
  False
  ((none -> none) .
   (none .
      (none .
         (HeatingSystem .
            (none . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) =
              ((s . dsh_sc_used0) + HeatingSystem) and
              (sn . dsh_sc_used1) = (s . dsh_sc_used1))
       )

}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T11_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Controller_On_Heater_Active &
   (sn . dsh_conf0))
  ((s . dsh_stable) = boolean/True)=>
    (!
       (HeatingSystem in dsh_scp0) and
       HeatingSystem_furnaceFault in
         (((s . dsh_events0) & DshEnvEvents) + dsh_genEvs0))
  else
    (HeatingSystem_furnaceFault in
       ((s . dsh_events0) + dsh_genEvs0))

}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T11 [s: one DshSnapshot, sn: one DshSnapshot] {
  s .
  HeatingSystem_Functioning_Controller_On_Heater_Active_T11_pre
  sn .
  (s .
     HeatingSystem_Functioning_Controller_On_Heater_Active_T11_post)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_pre [s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running
   & (s . dsh_conf0))
  ! (HeatingSystem in (s . dsh_sc_used0))
  ! (HeatingSystem_Functioning_Furnace in (s . dsh_sc_used0))
  ((s . dsh_stable) = boolean/True)=>
    (HeatingSystem_deactivate in
       ((s . dsh_events0) :> DshEnvEvents))
  else
    (HeatingSystem_deactivate in (s . dsh_events0))

}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_post [s: one DshSnapshot, sn: one DshSnapshot] {
  (sn . dsh_conf0) =
  (((((s . dsh_conf0) -
        HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off)
       -
       HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating)
      -
      HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)
     +
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off)
  (sn . dsh_conf1) = (s . dsh_conf1)
  ((none -> none) .
   (none .
      (none .
         (HeatingSystem_Functioning_Furnace .
            (none . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) =
              ((s . dsh_sc_used0) +
                 HeatingSystem_Functioning_Furnace) and
              (sn . dsh_sc_used1) = (s . dsh_sc_used1))
       )

}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running
   & (sn . dsh_conf0))
  !
  ((s . dsh_stable) = boolean/True) and
  HeatingSystem_deactivate in
    ((s . dsh_events0) + dsh_genEvs0)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4 [s: one DshSnapshot, sn: one DshSnapshot] {
  s .
  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_pre
  sn .
  (s .
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_post)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_pre [s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running
   & (s . dsh_conf0))
  ! (HeatingSystem in (s . dsh_sc_used0))
  ((s . dsh_stable) = boolean/True)=>
    (HeatingSystem_furnaceFault in
       ((s . dsh_events0) :> DshEnvEvents))
  else
    (HeatingSystem_furnaceFault in (s . dsh_events0))

}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_post [s: one DshSnapshot, sn: one DshSnapshot] {
  (sn . dsh_conf0) =
  (((((((((s . dsh_conf0) -
            HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off)
           -
           HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating)
          -
          HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)
         - HeatingSystem_Functioning_Controller_Off) -
        HeatingSystem_Functioning_Controller_On_Idle) -
       HeatingSystem_Functioning_Controller_On_Heater_Active)
      - HeatingSystem_ERROR) + HeatingSystem_ERROR)
  (sn . dsh_conf1) =
  (((((s . dsh_conf1) -
        (Identifier ->
           HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
       -
       (Identifier ->
          HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))
      -
      (Identifier ->
         HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
     -
     (Identifier ->
        HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))
  ((none -> none) .
   (none .
      (none .
         (HeatingSystem .
            (none . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) =
              ((s . dsh_sc_used0) + HeatingSystem) and
              (sn . dsh_sc_used1) = (s . dsh_sc_used1))
       )

}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running
   & (sn . dsh_conf0))
  ((s . dsh_stable) = boolean/True)=>
    (!
       (HeatingSystem in dsh_scp0) and
       HeatingSystem_furnaceFault in
         (((s . dsh_events0) & DshEnvEvents) + dsh_genEvs0))
  else
    (HeatingSystem_furnaceFault in
       ((s . dsh_events0) + dsh_genEvs0))

}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5 [s: one DshSnapshot, sn: one DshSnapshot] {
  s .
  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_pre
  sn .
  (s .
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_post)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_pre [s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating
   & (s . dsh_conf0))
  ! (HeatingSystem in (s . dsh_sc_used0))
  ! (HeatingSystem_Functioning_Furnace in (s . dsh_sc_used0))
}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_post [s: one DshSnapshot, sn: one DshSnapshot] {
  (sn . dsh_conf0) =
  (((((s . dsh_conf0) -
        HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off)
       -
       HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating)
      -
      HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)
     +
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)
  (sn . dsh_conf1) = (s . dsh_conf1)
  ((none -> none) .
   (none .
      (HeatingSystem_furnaceRunning .
         (HeatingSystem_Functioning_Furnace .
            (none . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) =
              HeatingSystem_furnaceRunning and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              (HeatingSystem_furnaceRunning +
                 ((s . dsh_events0) :> DshIntEvents)) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) =
              HeatingSystem_furnaceRunning and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_events0) =
              ((s . dsh_events0) +
                 HeatingSystem_furnaceRunning) and
              (sn . dsh_sc_used0) =
                ((s . dsh_sc_used0) +
                   HeatingSystem_Functioning_Furnace) and
              (sn . dsh_sc_used1) = (s . dsh_sc_used1))
       )

}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating
   & (sn . dsh_conf0))
  { (s . dsh_stable) = boolean/True and
    !
    (HeatingSystem in dsh_scp0) and
    !
    (HeatingSystem_Functioning_Furnace in dsh_scp0) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3 [s: one DshSnapshot, sn: one DshSnapshot] {
  s .
  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_pre
  sn .
  (s .
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_post)
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_pre [s: one DshSnapshot, p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat)
   & (s . dsh_conf1))
  !
((p0_Identifier .
    (s . HeatingSystem_Functioning_Room_desiredTemp)).((p0_Identifier
                                                          .
                                                          (s
                                                             .
                                                             HeatingSystem_Functioning_Room_actualTemp)).lt))
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
((p0_Identifier -> HeatingSystem_Functioning_Room) in
   (s . dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
     +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
  (p0_Identifier .
   (sn . HeatingSystem_Functioning_Room_actualTemp)) =
  ((p0_Identifier .
      (s . HeatingSystem_Functioning_Room_actualTemp)).temp/prev)
  ((none -> none) .
   ((p0_Identifier -> HeatingSystem_Functioning_Room) .
      (none .
         (none .
            (p0_Identifier . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_Room)))
       )

}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat)
   & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (HeatingSystem in dsh_scp0) and
    !
    ((p0_Identifier -> HeatingSystem_Functioning_Room) in
       dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  p0_Identifier .
  (s .
     HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_pre)
  p0_Identifier .
  (sn .
     (s .
        HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_post))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_pre [s: one DshSnapshot, p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat)
   & (s . dsh_conf1))
  (p0_Identifier .
   (s . HeatingSystem_Functioning_Room_desiredTemp)).((p0_Identifier
                                                         .
                                                         (s
                                                            .
                                                            HeatingSystem_Functioning_Room_actualTemp)).lt)
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
((p0_Identifier -> HeatingSystem_Functioning_Room) in
   (s . dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  ((((s . dsh_conf1) -
       (p0_Identifier ->
          HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
      -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))
     +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))
  ((none -> none) .
   ((p0_Identifier -> HeatingSystem_Functioning_Room) .
      (none .
         (none .
            (p0_Identifier . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_Room)))
       )

}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat)
   & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (HeatingSystem in dsh_scp0) and
    !
    ((p0_Identifier -> HeatingSystem_Functioning_Room) in
       dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12 [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  p0_Identifier .
  (s .
     HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_pre)
  p0_Identifier .
  (sn .
     (s .
        HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_post))
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_pre [s: one DshSnapshot, p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool)
   & (s . dsh_conf1))
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
((p0_Identifier -> HeatingSystem_Functioning_Room) in
   (s . dsh_sc_used1))
  ((s . dsh_stable) = boolean/True)=>
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForCool) in
       ((s . dsh_events1) :> DshEnvEvents))
  else
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForCool) in
       (s . dsh_events1))

}


pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))
     +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))
  (p0_Identifier .
   (sn . HeatingSystem_Functioning_Room_valvePos)) = CLOSED
  ((none -> none) .
   ((p0_Identifier -> HeatingSystem_Functioning_Room) .
      (none .
         (none .
            (p0_Identifier . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_Room)))
       )

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool)
   & (sn . dsh_conf1))
  ((s . dsh_stable) = boolean/True)=>
    (!
       (HeatingSystem in dsh_scp0) and
       !
       ((p0_Identifier -> HeatingSystem_Functioning_Room) in
          dsh_scp1) and
       (p0_Identifier ->
          HeatingSystem_Functioning_Room_waitedForCool) in
         (((s . dsh_events1) & DshEnvEvents) + dsh_genEvs1))
  else
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForCool) in
       ((s . dsh_events1) + dsh_genEvs1))

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17 [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  p0_Identifier .
  (s .
     HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_pre)
  p0_Identifier .
  (sn .
     (s .
        HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_post))
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_pre [s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off
   & (s . dsh_conf0))
  ! (HeatingSystem in (s . dsh_sc_used0))
  ! (HeatingSystem_Functioning_Furnace in (s . dsh_sc_used0))
  ((s . dsh_stable) = boolean/True)=>
    (HeatingSystem_activate in
       ((s . dsh_events0) :> DshEnvEvents))
  else
    (HeatingSystem_activate in (s . dsh_events0))

}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_post [s: one DshSnapshot, sn: one DshSnapshot] {
  (sn . dsh_conf0) =
  (((((s . dsh_conf0) -
        HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off)
       -
       HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating)
      -
      HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)
     +
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating)
  (sn . dsh_conf1) = (s . dsh_conf1)
  ((none -> none) .
   (none .
      (none .
         (HeatingSystem_Functioning_Furnace .
            (none . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) =
              ((s . dsh_sc_used0) +
                 HeatingSystem_Functioning_Furnace) and
              (sn . dsh_sc_used1) = (s . dsh_sc_used1))
       )

}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off
   & (sn . dsh_conf0))
  !
  ((s . dsh_stable) = boolean/True) and
  HeatingSystem_activate in
    ((s . dsh_events0) + dsh_genEvs0)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1 [s: one DshSnapshot, sn: one DshSnapshot] {
  s .
  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_pre
  sn .
  (s .
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_post)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_pre [s: one DshSnapshot, p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool)
   & (s . dsh_conf1))
  !
((p0_Identifier .
    (s . HeatingSystem_Functioning_Room_desiredTemp)).((p0_Identifier
                                                          .
                                                          (s
                                                             .
                                                             HeatingSystem_Functioning_Room_actualTemp)).gt))
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
((p0_Identifier -> HeatingSystem_Functioning_Room) in
   (s . dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  ((((s . dsh_conf1) -
       (p0_Identifier ->
          HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
      -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))
     +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
  ((none -> none) .
   ((p0_Identifier -> HeatingSystem_Functioning_Room) .
      (none .
         (none .
            (p0_Identifier . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_Room)))
       )

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool)
   & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (HeatingSystem in dsh_scp0) and
    !
    ((p0_Identifier -> HeatingSystem_Functioning_Room) in
       dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16 [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  p0_Identifier .
  (s .
     HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_pre)
  p0_Identifier .
  (sn .
     (s .
        HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_post))
}

pred HeatingSystem_ERROR_T19_pre [s: one DshSnapshot] {
  some (HeatingSystem_ERROR & (s . dsh_conf0))
  ! (HeatingSystem in (s . dsh_sc_used0))
  ((s . dsh_stable) = boolean/True)=>
    (HeatingSystem_heatSwitchOn in
       ((s . dsh_events0) :> DshEnvEvents))
  else
    (HeatingSystem_heatSwitchOn in (s . dsh_events0))

}


pred HeatingSystem_ERROR_T19_post [s: one DshSnapshot, sn: one DshSnapshot] {
  (sn . dsh_conf0) =
  (((((((((s . dsh_conf0) -
            HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off)
           -
           HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating)
          -
          HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)
         - HeatingSystem_Functioning_Controller_Off) -
        HeatingSystem_Functioning_Controller_On_Idle) -
       HeatingSystem_Functioning_Controller_On_Heater_Active)
      - HeatingSystem_ERROR) +
     (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off
        + HeatingSystem_Functioning_Controller_Off))
  (sn . dsh_conf1) =
  ((((((s . dsh_conf1) -
         (Identifier ->
            HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
        -
        (Identifier ->
           HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))
       -
       (Identifier ->
          HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
      -
      (Identifier ->
         HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))
     +
     (Identifier ->
        HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
  ((none -> none) .
   (none .
      (none .
         (HeatingSystem .
            (none . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) =
              ((s . dsh_sc_used0) + HeatingSystem) and
              (sn . dsh_sc_used1) = (s . dsh_sc_used1))
       )

}

pred HeatingSystem_ERROR_T19_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some (HeatingSystem_ERROR & (sn . dsh_conf0))
  ((s . dsh_stable) = boolean/True)=>
    (!
       (HeatingSystem in dsh_scp0) and
       HeatingSystem_heatSwitchOn in
         (((s . dsh_events0) & DshEnvEvents) + dsh_genEvs0))
  else
    (HeatingSystem_heatSwitchOn in
       ((s . dsh_events0) + dsh_genEvs0))

}

pred HeatingSystem_ERROR_T19 [s: one DshSnapshot, sn: one DshSnapshot] {
  s . HeatingSystem_ERROR_T19_pre
  sn . (s . HeatingSystem_ERROR_T19_post)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_pre [s: one DshSnapshot, p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool)
   & (s . dsh_conf1))
  (p0_Identifier .
   (s . HeatingSystem_Functioning_Room_valvePos)) = CLOSED
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
((p0_Identifier -> HeatingSystem_Functioning_Room) in
   (s . dsh_sc_used1))
  ((s . dsh_stable) = boolean/True)=>
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForCool) in
       ((s . dsh_events1) :> DshEnvEvents))
  else
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForCool) in
       (s . dsh_events1))

}


pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  ((((((s . dsh_conf1) -
         (p0_Identifier ->
            HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
        -
        (p0_Identifier ->
           HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))
       -
       (p0_Identifier ->
          HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
      -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))
     +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
  (p0_Identifier .
   (sn . HeatingSystem_Functioning_Room_requestHeat)) =
  False and
  (p0_Identifier .
     (sn . HeatingSystem_Functioning_Room_actualTemp)) =
    (p0_Identifier .
       (s . HeatingSystem_Functioning_Room_desiredTemp))
  ((none -> none) .
   ((p0_Identifier -> HeatingSystem_Functioning_Room) .
      (none .
         (none .
            (p0_Identifier . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_Room)))
       )

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool)
   & (sn . dsh_conf1))
  ((s . dsh_stable) = boolean/True)=>
    (!
       (HeatingSystem in dsh_scp0) and
       !
       ((p0_Identifier -> HeatingSystem_Functioning_Room) in
          dsh_scp1) and
       (p0_Identifier ->
          HeatingSystem_Functioning_Room_waitedForCool) in
         (((s . dsh_events1) & DshEnvEvents) + dsh_genEvs1))
  else
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForCool) in
       ((s . dsh_events1) + dsh_genEvs1))

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18 [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  p0_Identifier .
  (s .
     HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_pre)
  p0_Identifier .
  (sn .
     (s .
        HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_post))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_pre [s: one DshSnapshot, p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat)
   & (s . dsh_conf1))
  (p0_Identifier .
   (s . HeatingSystem_Functioning_Room_valvePos)) = CLOSED
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
((p0_Identifier -> HeatingSystem_Functioning_Room) in
   (s . dsh_sc_used1))
  ((s . dsh_stable) = boolean/True)=>
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForWarmth) in
       ((s . dsh_events1) :> DshEnvEvents))
  else
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForWarmth) in
       (s . dsh_events1))

}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))
     +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))
  (p0_Identifier .
   (sn . HeatingSystem_Functioning_Room_valvePos)) = OPEN
  ((none -> none) .
   ((p0_Identifier -> HeatingSystem_Functioning_Room) .
      (none .
         (none .
            (p0_Identifier . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_Room)))
       )

}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat)
   & (sn . dsh_conf1))
  ((s . dsh_stable) = boolean/True)=>
    (!
       (HeatingSystem in dsh_scp0) and
       !
       ((p0_Identifier -> HeatingSystem_Functioning_Room) in
          dsh_scp1) and
       (p0_Identifier ->
          HeatingSystem_Functioning_Room_waitedForWarmth) in
         (((s . dsh_events1) & DshEnvEvents) + dsh_genEvs1))
  else
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForWarmth) in
       ((s . dsh_events1) + dsh_genEvs1))

}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14 [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  p0_Identifier .
  (s .
     HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_pre)
  p0_Identifier .
  (sn .
     (s .
        HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_post))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_pre [s: one DshSnapshot, p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat)
   & (s . dsh_conf1))
  (p0_Identifier .
   (s . HeatingSystem_Functioning_Room_valvePos)) = OPEN and
  (s . HeatingSystem_Functioning_Controller_controllerOn) =
    True
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
((p0_Identifier -> HeatingSystem_Functioning_Room) in
   (s . dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  ((((((s . dsh_conf1) -
         (p0_Identifier ->
            HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
        -
        (p0_Identifier ->
           HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))
       -
       (p0_Identifier ->
          HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
      -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))
     +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
  (p0_Identifier .
   (sn . HeatingSystem_Functioning_Room_requestHeat)) = True
  ((none -> none) .
   ((p0_Identifier -> HeatingSystem_Functioning_Room) .
      (none .
         (none .
            (p0_Identifier . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_Room)))
       )

}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat)
   & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (HeatingSystem in dsh_scp0) and
    !
    ((p0_Identifier -> HeatingSystem_Functioning_Room) in
       dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15 [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  p0_Identifier .
  (s .
     HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_pre)
  p0_Identifier .
  (sn .
     (s .
        HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_post))
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_pre [s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating
   & (s . dsh_conf0))
  ! (HeatingSystem in (s . dsh_sc_used0))
  ! (HeatingSystem_Functioning_Furnace in (s . dsh_sc_used0))
  ((s . dsh_stable) = boolean/True)=>
    (HeatingSystem_deactivate in
       ((s . dsh_events0) :> DshEnvEvents))
  else
    (HeatingSystem_deactivate in (s . dsh_events0))

}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_post [s: one DshSnapshot, sn: one DshSnapshot] {
  (sn . dsh_conf0) =
  (((((s . dsh_conf0) -
        HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off)
       -
       HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating)
      -
      HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)
     +
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off)
  (sn . dsh_conf1) = (s . dsh_conf1)
  ((none -> none) .
   (none .
      (none .
         (HeatingSystem_Functioning_Furnace .
            (none . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) =
              ((s . dsh_sc_used0) +
                 HeatingSystem_Functioning_Furnace) and
              (sn . dsh_sc_used1) = (s . dsh_sc_used1))
       )

}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating
   & (sn . dsh_conf0))
  !
  ((s . dsh_stable) = boolean/True) and
  HeatingSystem_deactivate in
    ((s . dsh_events0) + dsh_genEvs0)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2 [s: one DshSnapshot, sn: one DshSnapshot] {
  s .
  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_pre
  sn .
  (s .
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_post)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_pre [s: one DshSnapshot, p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating)
   & (s . dsh_conf1))
  (p0_Identifier .
   (s . HeatingSystem_Functioning_Room_desiredTemp)).((p0_Identifier
                                                         .
                                                         (s
                                                            .
                                                            HeatingSystem_Functioning_Room_actualTemp)).gt)
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
((p0_Identifier -> HeatingSystem_Functioning_Room) in
   (s . dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  ((((s . dsh_conf1) -
       (p0_Identifier ->
          HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
      -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))
     +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))
  (p0_Identifier .
   (sn . HeatingSystem_Functioning_Room_valvePos)) = CLOSED
  ((none -> none) .
   ((p0_Identifier -> HeatingSystem_Functioning_Room) .
      (none .
         (none .
            (p0_Identifier . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_Room)))
       )

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating)
   & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (HeatingSystem in dsh_scp0) and
    !
    ((p0_Identifier -> HeatingSystem_Functioning_Room) in
       dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15 [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  p0_Identifier .
  (s .
     HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_pre)
  p0_Identifier .
  (sn .
     (s .
        HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_post))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_pre [s: one DshSnapshot, p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat)
   & (s . dsh_conf1))
  !
((p0_Identifier .
    (s . HeatingSystem_Functioning_Room_desiredTemp)).((p0_Identifier
                                                          .
                                                          (s
                                                             .
                                                             HeatingSystem_Functioning_Room_actualTemp)).lt))
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
((p0_Identifier -> HeatingSystem_Functioning_Room) in
   (s . dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  ((((s . dsh_conf1) -
       (p0_Identifier ->
          HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
      -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))
     +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
  ((none -> none) .
   ((p0_Identifier -> HeatingSystem_Functioning_Room) .
      (none .
         (none .
            (p0_Identifier . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_Room)))
       )

}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat)
   & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (HeatingSystem in dsh_scp0) and
    !
    ((p0_Identifier -> HeatingSystem_Functioning_Room) in
       dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13 [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  p0_Identifier .
  (s .
     HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_pre)
  p0_Identifier .
  (sn .
     (s .
        HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_post))
}

pred HeatingSystem_Functioning_Controller_On_Idle_T9_pre [s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Controller_On_Idle &
   (s . dsh_conf0))
  (some r: Identifier | (r .
                         (s .
                            HeatingSystem_Functioning_Room_requestHeat))
                        = True)
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
(HeatingSystem_Functioning_Controller in (s . dsh_sc_used0))
}


pred HeatingSystem_Functioning_Controller_On_Idle_T9_post [s: one DshSnapshot, sn: one DshSnapshot] {
  (sn . dsh_conf0) =
  ((((s . dsh_conf0) -
       HeatingSystem_Functioning_Controller_On_Idle) -
      HeatingSystem_Functioning_Controller_On_Heater_Active)
     + HeatingSystem_Functioning_Controller_On_Heater_Active)
  (sn . dsh_conf1) = (s . dsh_conf1)
  ((none -> none) .
   (none .
      (HeatingSystem_activate .
         (HeatingSystem_Functioning_Controller .
            (none . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) =
              HeatingSystem_activate and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              (HeatingSystem_activate +
                 ((s . dsh_events0) :> DshIntEvents)) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) =
              HeatingSystem_activate and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_events0) =
              ((s . dsh_events0) + HeatingSystem_activate) and
              (sn . dsh_sc_used0) =
                ((s . dsh_sc_used0) +
                   HeatingSystem_Functioning_Controller) and
              (sn . dsh_sc_used1) = (s . dsh_sc_used1))
       )

}

pred HeatingSystem_Functioning_Controller_On_Idle_T9_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Controller_On_Idle &
   (sn . dsh_conf0))
  { (s . dsh_stable) = boolean/True and
    !
    (HeatingSystem in dsh_scp0) and
    !
    (HeatingSystem_Functioning_Controller in dsh_scp0) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred HeatingSystem_Functioning_Controller_On_Idle_T9 [s: one DshSnapshot, sn: one DshSnapshot] {
  s . HeatingSystem_Functioning_Controller_On_Idle_T9_pre
  sn .
  (s . HeatingSystem_Functioning_Controller_On_Idle_T9_post)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_pre [s: one DshSnapshot, p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating)
   & (s . dsh_conf1))
  !
((p0_Identifier .
    (s . HeatingSystem_Functioning_Room_desiredTemp)).((p0_Identifier
                                                          .
                                                          (s
                                                             .
                                                             HeatingSystem_Functioning_Room_actualTemp)).gt))
  ! (HeatingSystem in (s . dsh_sc_used0))
  !
((p0_Identifier -> HeatingSystem_Functioning_Room) in
   (s . dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_post [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  (sn . dsh_conf0) = (s . dsh_conf0)
  (sn . dsh_conf1) =
  (((s . dsh_conf1) -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
     +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
  (p0_Identifier .
   (sn . HeatingSystem_Functioning_Room_actualTemp)) =
  ((p0_Identifier .
      (s . HeatingSystem_Functioning_Room_actualTemp)).temp/next)
  ((none -> none) .
   ((p0_Identifier -> HeatingSystem_Functioning_Room) .
      (none .
         (none .
            (p0_Identifier . (sn . (s . _testIfNextStable)))))))=>
    ((sn . dsh_stable) = boolean/True and
       (sn . dsh_sc_used0) = none and
       (sn . dsh_sc_used1) = none and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none))
         else
           (((sn . dsh_events0) :> DshIntEvents) =
              ((s . dsh_events0) :> DshIntEvents) and
              ((sn . dsh_events1) :> DshIntEvents) =
                ((s . dsh_events1) :> DshIntEvents))
       )
  else
    ((sn . dsh_stable) = boolean/False and
       ((s . dsh_stable) = boolean/True)=>
           (((sn . dsh_events0) :> DshIntEvents) = none and
              ((sn . dsh_events0) :> DshEnvEvents) =
                ((s . dsh_events0) :> DshEnvEvents) and
              (sn . dsh_sc_used0) = none and
              ((sn . dsh_events1) :> DshIntEvents) =
                (none -> none) and
              ((sn . dsh_events1) :> DshEnvEvents) =
                ((s . dsh_events1) :> DshEnvEvents) and
              (sn . dsh_sc_used1) = none)
         else
           ((sn . dsh_sc_used0) = (s . dsh_sc_used0) and
              (sn . dsh_sc_used1) =
                ((s . dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_Room)))
       )

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_enabledAfterStep [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating)
   & (sn . dsh_conf1))
  { (s . dsh_stable) = boolean/True and
    !
    (HeatingSystem in dsh_scp0) and
    !
    ((p0_Identifier -> HeatingSystem_Functioning_Room) in
       dsh_scp1) or
    !
    ((s . dsh_stable) = boolean/True) }
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier] {
  p0_Identifier .
  (s .
     HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_pre)
  p0_Identifier .
  (sn .
     (s .
        HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_post))
}

pred _testIfNextStable [s: one DshSnapshot, sn: one DshSnapshot, p0_Identifier: one Identifier, dsh_scp0: DshStates, dsh_genEvs0: DshEvents, dsh_scp1: DshIds -> DshStates, dsh_genEvs1: DshIds -> DshEvents] {
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Controller_Off_T8_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Controller_On_Heater_Active_T10_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Controller_On_Heater_Active_T11_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s . HeatingSystem_ERROR_T19_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Controller_On_Idle_T9_enabledAfterStep))))))
  !
(dsh_genEvs1 .
   (dsh_scp1 .
      (dsh_genEvs0 .
         (dsh_scp0 .
            (sn .
               (s .
                  HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_enabledAfterStep))))))
}

pred dsh_small_step [s: one DshSnapshot, sn: one DshSnapshot] {
  (some p0_Identifier: one
  Identifier | { sn .
                   (s .
                      HeatingSystem_Functioning_Controller_Off_T8) or
                   sn .
                     (s .
                        HeatingSystem_Functioning_Controller_On_Heater_Active_T10) or
                   sn .
                     (s .
                        HeatingSystem_Functioning_Controller_On_Heater_Active_T11) or
                   sn .
                     (s .
                        HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4) or
                   sn .
                     (s .
                        HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5) or
                   sn .
                     (s .
                        HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3) or
                   p0_Identifier .
                     (sn .
                        (s .
                           HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom)) or
                   p0_Identifier .
                     (sn .
                        (s .
                           HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12)) or
                   p0_Identifier .
                     (sn .
                        (s .
                           HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17)) or
                   sn .
                     (s .
                        HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1) or
                   p0_Identifier .
                     (sn .
                        (s .
                           HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16)) or
                   sn . (s . HeatingSystem_ERROR_T19) or
                   p0_Identifier .
                     (sn .
                        (s .
                           HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18)) or
                   p0_Identifier .
                     (sn .
                        (s .
                           HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14)) or
                   p0_Identifier .
                     (sn .
                        (s .
                           HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15)) or
                   sn .
                     (s .
                        HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2) or
                   p0_Identifier .
                     (sn .
                        (s .
                           HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15)) or
                   p0_Identifier .
                     (sn .
                        (s .
                           HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13)) or
                   sn .
                     (s .
                        HeatingSystem_Functioning_Controller_On_Idle_T9) or
                   p0_Identifier .
                     (sn .
                        (s .
                           HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom)) })
}

fact dsh_traces_fact {  DshSnapshot/first . dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s . DshSnapshot/next)
                                       .
                                       (s . dsh_small_step))
}

