/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-28 17:41:13
*/

open util/ordering[Temp] as temp

open util/boolean
open util/tcmc[DshSnapshot]

sig Temp{}
abstract sig ValvePos {}
one sig OPEN, HALF, CLOSED extends ValvePos {}

abstract sig DshStates {}
abstract sig HeatingSystem extends DshStates {} 
abstract sig DshScopes {}
one sig HeatingSystemScope extends DshScopes {} 
one sig HeatingSystem_FunctioningScope extends DshScopes {} 
abstract sig HeatingSystem_Functioning extends HeatingSystem {} 
one sig HeatingSystem_Functioning_FurnaceScope extends DshScopes {} 
abstract sig HeatingSystem_Functioning_Furnace extends HeatingSystem_Functioning {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_NormalScope extends DshScopes {} 
abstract sig HeatingSystem_Functioning_Furnace_Furnace_Normal extends HeatingSystem_Functioning_Furnace {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_OffScope extends DshScopes {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off extends HeatingSystem_Functioning_Furnace_Furnace_Normal {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_ActivatingScope extends DshScopes {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating extends HeatingSystem_Functioning_Furnace_Furnace_Normal {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_RunningScope extends DshScopes {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running extends HeatingSystem_Functioning_Furnace_Furnace_Normal {} 
one sig HeatingSystem_Functioning_ControllerScope extends DshScopes {} 
abstract sig HeatingSystem_Functioning_Controller extends HeatingSystem_Functioning {} 
one sig HeatingSystem_Functioning_Controller_OffScope extends DshScopes {} 
one sig HeatingSystem_Functioning_Controller_Off extends HeatingSystem_Functioning_Controller {} 
one sig HeatingSystem_Functioning_Controller_OnScope extends DshScopes {} 
abstract sig HeatingSystem_Functioning_Controller_On extends HeatingSystem_Functioning_Controller {} 
one sig HeatingSystem_Functioning_Controller_On_IdleScope extends DshScopes {} 
one sig HeatingSystem_Functioning_Controller_On_Idle extends HeatingSystem_Functioning_Controller_On {} 
one sig HeatingSystem_Functioning_Controller_On_Heater_ActiveScope extends DshScopes {} 
one sig HeatingSystem_Functioning_Controller_On_Heater_Active extends HeatingSystem_Functioning_Controller_On {} 
one sig HeatingSystem_Functioning_RoomScope extends DshScopes {} 
abstract sig HeatingSystem_Functioning_Room extends HeatingSystem_Functioning {} 
one sig HeatingSystem_Functioning_Room_No_Heat_RequestScope extends DshScopes {} 
abstract sig HeatingSystem_Functioning_Room_No_Heat_Request extends HeatingSystem_Functioning_Room {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_HeatScope extends DshScopes {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat extends HeatingSystem_Functioning_Room_No_Heat_Request {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_HeatScope extends DshScopes {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat extends HeatingSystem_Functioning_Room_No_Heat_Request {} 
one sig HeatingSystem_Functioning_Room_Heat_RequestedScope extends DshScopes {} 
abstract sig HeatingSystem_Functioning_Room_Heat_Requested extends HeatingSystem_Functioning_Room {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Idle_HeatingScope extends DshScopes {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating extends HeatingSystem_Functioning_Room_Heat_Requested {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_CoolScope extends DshScopes {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool extends HeatingSystem_Functioning_Room_Heat_Requested {} 
one sig HeatingSystem_ERRORScope extends DshScopes {} 
one sig HeatingSystem_ERROR extends HeatingSystem {} 

abstract sig Transitions {}
one sig NO_TRANS extends Transitions {} 
one sig HeatingSystem_Functioning_Controller_Off_T8 extends Transitions {} 
one sig HeatingSystem_Functioning_Controller_On_Heater_Active_T10 extends Transitions {} 
one sig HeatingSystem_Functioning_Controller_On_Heater_Active_T11 extends Transitions {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4 extends Transitions {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5 extends Transitions {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3 extends Transitions {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom extends Transitions {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12 extends Transitions {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17 extends Transitions {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1 extends Transitions {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16 extends Transitions {} 
one sig HeatingSystem_ERROR_T19 extends Transitions {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18 extends Transitions {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14 extends Transitions {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15 extends Transitions {} 
one sig HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2 extends Transitions {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15 extends Transitions {} 
one sig HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13 extends Transitions {} 
one sig HeatingSystem_Functioning_Controller_On_Idle_T9 extends Transitions {} 
one sig HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom extends Transitions {} 

abstract sig DshIds {}
sig Identifier extends DshIds {} 

abstract sig DshEvents {}
abstract sig DshIntEvents extends DshEvents {} 
one sig HeatingSystem_activate extends DshIntEvents {} 
one sig HeatingSystem_deactivate extends DshIntEvents {} 
one sig HeatingSystem_furnaceRunning extends DshIntEvents {} 
one sig HeatingSystem_furnaceNotRunning extends DshIntEvents {} 
one sig HeatingSystem_furnaceReset extends DshIntEvents {} 
abstract sig DshEnvEvents extends DshEvents {} 
one sig HeatingSystem_Functioning_Room_waitedForWarmth extends DshEnvEvents {} 
one sig HeatingSystem_Functioning_Room_waitedForCool extends DshEnvEvents {} 
one sig HeatingSystem_Reset extends DshEnvEvents {} 
one sig HeatingSystem_TurnOn extends DshEnvEvents {} 
one sig HeatingSystem_furnaceFault extends DshEnvEvents {} 
one sig HeatingSystem_userReset extends DshEnvEvents {} 
one sig HeatingSystem_heatSwitchOn extends DshEnvEvents {} 

sig DshSnapshot {
  dsh_sc_used0: set DshScopes,
  dsh_conf0: set DshStates,
  dsh_taken0: set Transitions,
  dsh_events0: set DshEvents,
  dsh_sc_used1: DshIds -> DshScopes,
  dsh_conf1: DshIds -> DshStates,
  dsh_taken1: DshIds -> Transitions,
  dsh_events1: DshIds -> DshEvents,
  dsh_stable: one boolean/Bool,
  HeatingSystem_Functioning_Controller_controllerOn: one Bool,
  HeatingSystem_Functioning_Room_actualTemp: Identifier -> one
                                             Temp,
  HeatingSystem_Functioning_Room_desiredTemp: Identifier ->
                                              one Temp,
  HeatingSystem_Functioning_Room_valvePos: Identifier -> one
                                           ValvePos,
  HeatingSystem_Functioning_Room_requestHeat: Identifier ->
                                              one Bool
}

pred dsh_initial [
	s: one DshSnapshot] {
  (all p0_Identifier: one
  Identifier | (s.dsh_conf0) =
                 (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off +
                    HeatingSystem_Functioning_Controller_Off) &&
                 (s.dsh_conf1) =
                   (Identifier ->
                      HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) &&
                 (s.dsh_sc_used0) = none &&
                 (s.dsh_taken0) = NO_TRANS &&
                 ((s.dsh_events0) :> DshIntEvents) = none &&
                 (s.dsh_sc_used1) = (none -> none) &&
                 (s.dsh_taken1) = (none -> none) &&
                 (s.HeatingSystem_Functioning_Controller_controllerOn) =
                   False &&
                 (p0_Identifier.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                   False &&
                 (p0_Identifier.(s.HeatingSystem_Functioning_Room_valvePos)) =
                   CLOSED)
  (s.dsh_stable).boolean/isTrue
}

pred HeatingSystem_Functioning_Controller_Off_T8_pre [
	s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Controller_Off & (s.dsh_conf0))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !(HeatingSystem_Functioning_ControllerScope in
    (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (HeatingSystem_heatSwitchOn in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (HeatingSystem_heatSwitchOn in (s.dsh_events0))}

}


pred HeatingSystem_Functioning_Controller_Off_T8_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      ((HeatingSystem_Functioning_Controller_Off +
          HeatingSystem_Functioning_Controller_On_Idle) +
         HeatingSystem_Functioning_Controller_On_Heater_Active)) +
     HeatingSystem_Functioning_Controller_On_Idle)
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.HeatingSystem_Functioning_Controller_controllerOn) =
  True
  (sn.dsh_taken0) =
  HeatingSystem_Functioning_Controller_Off_T8
  (sn.dsh_taken1) = (none -> none)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((none -> none).(HeatingSystem_furnaceReset.(HeatingSystem_Functioning_Controller.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              HeatingSystem_furnaceReset)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (HeatingSystem_furnaceReset +
                 ((s.dsh_events0) :> DshIntEvents)))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              HeatingSystem_furnaceReset &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) + HeatingSystem_furnaceReset) &&
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) +
                   HeatingSystem_Functioning_ControllerScope) &&
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))}
       )}

}

pred HeatingSystem_Functioning_Controller_Off_T8_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Controller_Off & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(HeatingSystem in sc0) &&
       !(HeatingSystem_Functioning_Controller in sc0) &&
       HeatingSystem_heatSwitchOn in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (HeatingSystem_heatSwitchOn in
       ((s.dsh_events0) + genEvs0))}

}

pred HeatingSystem_Functioning_Controller_Off_T8 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.HeatingSystem_Functioning_Controller_Off_T8_pre
  sn.(s.HeatingSystem_Functioning_Controller_Off_T8_post)
}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T10_pre [
	s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Controller_On_Heater_Active &
   (s.dsh_conf0))
  (no r: Identifier | (r.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                      True)
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !(HeatingSystem_Functioning_ControllerScope in
    (s.dsh_sc_used0))
}


pred HeatingSystem_Functioning_Controller_On_Heater_Active_T10_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (HeatingSystem_Functioning_Controller_On_Idle +
         HeatingSystem_Functioning_Controller_On_Heater_Active)) +
     HeatingSystem_Functioning_Controller_On_Idle)
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.dsh_taken0) =
  HeatingSystem_Functioning_Controller_On_Heater_Active_T10
  (sn.dsh_taken1) = (none -> none)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((none -> none).(HeatingSystem_deactivate.(HeatingSystem_Functioning_Controller.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              HeatingSystem_deactivate)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (HeatingSystem_deactivate +
                 ((s.dsh_events0) :> DshIntEvents)))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              HeatingSystem_deactivate &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) + HeatingSystem_deactivate) &&
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) +
                   HeatingSystem_Functioning_ControllerScope) &&
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))}
       )}

}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T10_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Controller_On_Heater_Active &
   (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue &&
    !(HeatingSystem in sc0) &&
    !(HeatingSystem_Functioning_Controller in sc0) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T10 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.HeatingSystem_Functioning_Controller_On_Heater_Active_T10_pre
  sn.(s.HeatingSystem_Functioning_Controller_On_Heater_Active_T10_post)
}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T11_pre [
	s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Controller_On_Heater_Active &
   (s.dsh_conf0))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (HeatingSystem_furnaceFault in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (HeatingSystem_furnaceFault in (s.dsh_events0))}

}


pred HeatingSystem_Functioning_Controller_On_Heater_Active_T11_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      ((((((HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off +
              HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating) +
             HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running) +
            HeatingSystem_Functioning_Controller_Off) +
           HeatingSystem_Functioning_Controller_On_Idle) +
          HeatingSystem_Functioning_Controller_On_Heater_Active) +
         HeatingSystem_ERROR)) + HeatingSystem_ERROR)
  (sn.dsh_conf1) =
  ((s.dsh_conf1) -
     ((((Identifier ->
           HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) +
          (Identifier ->
             HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat)) +
         (Identifier ->
            HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating)) +
        (Identifier ->
           HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool)))
  (sn.HeatingSystem_Functioning_Controller_controllerOn) =
  False
  (sn.dsh_taken0) =
  HeatingSystem_Functioning_Controller_On_Heater_Active_T11
  (sn.dsh_taken1) = (none -> none)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((none -> none).(none.(HeatingSystem.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + HeatingSystemScope) &&
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))}
       )}

}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T11_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Controller_On_Heater_Active &
   (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(HeatingSystem in sc0) &&
       HeatingSystem_furnaceFault in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (HeatingSystem_furnaceFault in
       ((s.dsh_events0) + genEvs0))}

}

pred HeatingSystem_Functioning_Controller_On_Heater_Active_T11 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.HeatingSystem_Functioning_Controller_On_Heater_Active_T11_pre
  sn.(s.HeatingSystem_Functioning_Controller_On_Heater_Active_T11_post)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_pre [
	s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running &
   (s.dsh_conf0))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !(HeatingSystem_Functioning_FurnaceScope in (s.dsh_sc_used0))
  !((s.dsh_stable).boolean/isTrue) &&
  HeatingSystem_deactivate in (s.dsh_events0)
}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      ((HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off +
          HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating) +
         HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)) +
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off)
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.dsh_taken0) =
  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4
  (sn.dsh_taken1) = (none -> none)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((none -> none).(none.(HeatingSystem_Functioning_Furnace.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) +
                 HeatingSystem_Functioning_FurnaceScope) &&
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))}
       )}

}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running &
   (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) &&
  HeatingSystem_deactivate in ((s.dsh_events0) + genEvs0)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_pre
  sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_post)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_pre [
	s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running &
   (s.dsh_conf0))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (HeatingSystem_furnaceFault in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (HeatingSystem_furnaceFault in (s.dsh_events0))}

}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      ((((((HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off +
              HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating) +
             HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running) +
            HeatingSystem_Functioning_Controller_Off) +
           HeatingSystem_Functioning_Controller_On_Idle) +
          HeatingSystem_Functioning_Controller_On_Heater_Active) +
         HeatingSystem_ERROR)) + HeatingSystem_ERROR)
  (sn.dsh_conf1) =
  ((s.dsh_conf1) -
     ((((Identifier ->
           HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) +
          (Identifier ->
             HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat)) +
         (Identifier ->
            HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating)) +
        (Identifier ->
           HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool)))
  (sn.dsh_taken0) =
  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5
  (sn.dsh_taken1) = (none -> none)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((none -> none).(none.(HeatingSystem.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + HeatingSystemScope) &&
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))}
       )}

}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running &
   (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(HeatingSystem in sc0) &&
       HeatingSystem_furnaceFault in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (HeatingSystem_furnaceFault in
       ((s.dsh_events0) + genEvs0))}

}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_pre
  sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_post)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_pre [
	s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating &
   (s.dsh_conf0))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !(HeatingSystem_Functioning_FurnaceScope in (s.dsh_sc_used0))
}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      ((HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off +
          HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating) +
         HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)) +
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.dsh_taken0) =
  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3
  (sn.dsh_taken1) = (none -> none)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((none -> none).(HeatingSystem_furnaceRunning.(HeatingSystem_Functioning_Furnace.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              HeatingSystem_furnaceRunning)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (HeatingSystem_furnaceRunning +
                 ((s.dsh_events0) :> DshIntEvents)))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              HeatingSystem_furnaceRunning &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) +
                 HeatingSystem_furnaceRunning) &&
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) +
                   HeatingSystem_Functioning_FurnaceScope) &&
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))}
       )}

}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating &
   (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue &&
    !(HeatingSystem in sc0) &&
    !(HeatingSystem_Functioning_Furnace in sc0) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_pre
  sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_post)
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) &
   (s.dsh_conf1))
  !((p0_Identifier.(s.HeatingSystem_Functioning_Room_desiredTemp)).((p0_Identifier.(s.HeatingSystem_Functioning_Room_actualTemp)).lt))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> HeatingSystem_Functioning_RoomScope) in
    (s.dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat)) +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
  (p0_Identifier.(sn.HeatingSystem_Functioning_Room_actualTemp)) =
  ((p0_Identifier.(s.HeatingSystem_Functioning_Room_actualTemp)).temp/prev)
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier ->
     HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom)
  (all Identifier_aa: Identifier - p0_Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                                                   (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((p0_Identifier ->
                     HeatingSystem_Functioning_Room).(none.(none.(p0_Identifier.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_RoomScope)))}
       )}

}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(HeatingSystem in sc0) &&
    !((p0_Identifier -> HeatingSystem_Functioning_Room) in
        sc1) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_pre)
  p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_post))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) &
   (s.dsh_conf1))
  (p0_Identifier.(s.HeatingSystem_Functioning_Room_desiredTemp)).((p0_Identifier.(s.HeatingSystem_Functioning_Room_actualTemp)).lt)
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> HeatingSystem_Functioning_RoomScope) in
    (s.dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_Identifier ->
          HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) +
         (p0_Identifier ->
            HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))) +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier ->
     HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((p0_Identifier ->
                     HeatingSystem_Functioning_Room).(none.(none.(p0_Identifier.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_RoomScope)))}
       )}

}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(HeatingSystem in sc0) &&
    !((p0_Identifier -> HeatingSystem_Functioning_Room) in
        sc1) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_pre)
  p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_post))
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool) &
   (s.dsh_conf1))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> HeatingSystem_Functioning_RoomScope) in
    (s.dsh_sc_used1))
  {((s.dsh_stable).boolean/isTrue)=>
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForCool) in
       ((s.dsh_events1) :> DshEnvEvents))
  else
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForCool) in
       (s.dsh_events1))}

}


pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool)) +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))
  (p0_Identifier.(sn.HeatingSystem_Functioning_Room_valvePos)) =
  CLOSED
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier ->
     HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17)
  (all Identifier_aa: Identifier - p0_Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                                                   (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  {((none -> none).((p0_Identifier ->
                     HeatingSystem_Functioning_Room).(none.(none.(p0_Identifier.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_RoomScope)))}
       )}

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool) &
   (sn.dsh_conf1))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(HeatingSystem in sc0) &&
       !((p0_Identifier -> HeatingSystem_Functioning_Room) in
           sc1) &&
       (p0_Identifier ->
          HeatingSystem_Functioning_Room_waitedForCool) in
         (((s.dsh_events1) :> DshEnvEvents) + genEvs1))
  else
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForCool) in
       ((s.dsh_events1) + genEvs1))}

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_pre)
  p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_post))
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_pre [
	s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off &
   (s.dsh_conf0))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !(HeatingSystem_Functioning_FurnaceScope in (s.dsh_sc_used0))
  !((s.dsh_stable).boolean/isTrue) &&
  HeatingSystem_activate in (s.dsh_events0)
}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      ((HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off +
          HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating) +
         HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)) +
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating)
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.dsh_taken0) =
  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1
  (sn.dsh_taken1) = (none -> none)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((none -> none).(none.(HeatingSystem_Functioning_Furnace.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) +
                 HeatingSystem_Functioning_FurnaceScope) &&
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))}
       )}

}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off &
   (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) &&
  HeatingSystem_activate in ((s.dsh_events0) + genEvs0)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_pre
  sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_post)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool) &
   (s.dsh_conf1))
  !((p0_Identifier.(s.HeatingSystem_Functioning_Room_desiredTemp)).((p0_Identifier.(s.HeatingSystem_Functioning_Room_actualTemp)).gt))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> HeatingSystem_Functioning_RoomScope) in
    (s.dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_Identifier ->
          HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating) +
         (p0_Identifier ->
            HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))) +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier ->
     HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((p0_Identifier ->
                     HeatingSystem_Functioning_Room).(none.(none.(p0_Identifier.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_RoomScope)))}
       )}

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(HeatingSystem in sc0) &&
    !((p0_Identifier -> HeatingSystem_Functioning_Room) in
        sc1) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_pre)
  p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_post))
}

pred HeatingSystem_ERROR_T19_pre [
	s: one DshSnapshot] {
  some (HeatingSystem_ERROR & (s.dsh_conf0))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (HeatingSystem_heatSwitchOn in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (HeatingSystem_heatSwitchOn in (s.dsh_events0))}

}


pred HeatingSystem_ERROR_T19_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      ((((((HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off +
              HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating) +
             HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running) +
            HeatingSystem_Functioning_Controller_Off) +
           HeatingSystem_Functioning_Controller_On_Idle) +
          HeatingSystem_Functioning_Controller_On_Heater_Active) +
         HeatingSystem_ERROR)) +
     (HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off +
        HeatingSystem_Functioning_Controller_Off))
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((((Identifier ->
            HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) +
           (Identifier ->
              HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat)) +
          (Identifier ->
             HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating)) +
         (Identifier ->
            HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))) +
     (Identifier ->
        HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
  (sn.dsh_taken0) = HeatingSystem_ERROR_T19
  (sn.dsh_taken1) = (none -> none)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((none -> none).(none.(HeatingSystem.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + HeatingSystemScope) &&
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))}
       )}

}

pred HeatingSystem_ERROR_T19_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some (HeatingSystem_ERROR & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(HeatingSystem in sc0) &&
       HeatingSystem_heatSwitchOn in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (HeatingSystem_heatSwitchOn in
       ((s.dsh_events0) + genEvs0))}

}

pred HeatingSystem_ERROR_T19 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.HeatingSystem_ERROR_T19_pre
  sn.(s.HeatingSystem_ERROR_T19_post)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool) &
   (s.dsh_conf1))
  (p0_Identifier.(s.HeatingSystem_Functioning_Room_valvePos)) =
  CLOSED
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> HeatingSystem_Functioning_RoomScope) in
    (s.dsh_sc_used1))
  {((s.dsh_stable).boolean/isTrue)=>
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForCool) in
       ((s.dsh_events1) :> DshEnvEvents))
  else
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForCool) in
       (s.dsh_events1))}

}


pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((((p0_Identifier ->
            HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) +
           (p0_Identifier ->
              HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat)) +
          (p0_Identifier ->
             HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating)) +
         (p0_Identifier ->
            HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))) +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
  (p0_Identifier.(sn.HeatingSystem_Functioning_Room_requestHeat)) =
  False &&
  (p0_Identifier.(sn.HeatingSystem_Functioning_Room_actualTemp)) =
    (p0_Identifier.(s.HeatingSystem_Functioning_Room_desiredTemp))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier ->
     HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18)
  (all Identifier_aa: Identifier - p0_Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                                                   (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: Identifier - p0_Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                                                   (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((p0_Identifier ->
                     HeatingSystem_Functioning_Room).(none.(none.(p0_Identifier.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_RoomScope)))}
       )}

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool) &
   (sn.dsh_conf1))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(HeatingSystem in sc0) &&
       !((p0_Identifier -> HeatingSystem_Functioning_Room) in
           sc1) &&
       (p0_Identifier ->
          HeatingSystem_Functioning_Room_waitedForCool) in
         (((s.dsh_events1) :> DshEnvEvents) + genEvs1))
  else
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForCool) in
       ((s.dsh_events1) + genEvs1))}

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_pre)
  p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_post))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat) &
   (s.dsh_conf1))
  (p0_Identifier.(s.HeatingSystem_Functioning_Room_valvePos)) =
  CLOSED
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> HeatingSystem_Functioning_RoomScope) in
    (s.dsh_sc_used1))
  {((s.dsh_stable).boolean/isTrue)=>
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForWarmth) in
       ((s.dsh_events1) :> DshEnvEvents))
  else
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForWarmth) in
       (s.dsh_events1))}

}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat)) +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))
  (p0_Identifier.(sn.HeatingSystem_Functioning_Room_valvePos)) =
  OPEN
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier ->
     HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14)
  (all Identifier_aa: Identifier - p0_Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                                                   (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  {((none -> none).((p0_Identifier ->
                     HeatingSystem_Functioning_Room).(none.(none.(p0_Identifier.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_RoomScope)))}
       )}

}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat) &
   (sn.dsh_conf1))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(HeatingSystem in sc0) &&
       !((p0_Identifier -> HeatingSystem_Functioning_Room) in
           sc1) &&
       (p0_Identifier ->
          HeatingSystem_Functioning_Room_waitedForWarmth) in
         (((s.dsh_events1) :> DshEnvEvents) + genEvs1))
  else
    ((p0_Identifier ->
        HeatingSystem_Functioning_Room_waitedForWarmth) in
       ((s.dsh_events1) + genEvs1))}

}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_pre)
  p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_post))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat) &
   (s.dsh_conf1))
  (p0_Identifier.(s.HeatingSystem_Functioning_Room_valvePos)) =
  OPEN &&
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
    True
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> HeatingSystem_Functioning_RoomScope) in
    (s.dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((((p0_Identifier ->
            HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) +
           (p0_Identifier ->
              HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat)) +
          (p0_Identifier ->
             HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating)) +
         (p0_Identifier ->
            HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))) +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
  (p0_Identifier.(sn.HeatingSystem_Functioning_Room_requestHeat)) =
  True
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier ->
     HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15)
  (all Identifier_aa: Identifier - p0_Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                                                   (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((p0_Identifier ->
                     HeatingSystem_Functioning_Room).(none.(none.(p0_Identifier.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_RoomScope)))}
       )}

}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(HeatingSystem in sc0) &&
    !((p0_Identifier -> HeatingSystem_Functioning_Room) in
        sc1) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_pre)
  p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_post))
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_pre [
	s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating &
   (s.dsh_conf0))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !(HeatingSystem_Functioning_FurnaceScope in (s.dsh_sc_used0))
  !((s.dsh_stable).boolean/isTrue) &&
  HeatingSystem_deactivate in (s.dsh_events0)
}


pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      ((HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off +
          HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating) +
         HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running)) +
     HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off)
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.dsh_taken0) =
  HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2
  (sn.dsh_taken1) = (none -> none)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((none -> none).(none.(HeatingSystem_Functioning_Furnace.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) +
                 HeatingSystem_Functioning_FurnaceScope) &&
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))}
       )}

}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating &
   (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) &&
  HeatingSystem_deactivate in ((s.dsh_events0) + genEvs0)
}

pred HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_pre
  sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_post)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating) &
   (s.dsh_conf1))
  (p0_Identifier.(s.HeatingSystem_Functioning_Room_desiredTemp)).((p0_Identifier.(s.HeatingSystem_Functioning_Room_actualTemp)).gt)
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> HeatingSystem_Functioning_RoomScope) in
    (s.dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_Identifier ->
          HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating) +
         (p0_Identifier ->
            HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))) +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool))
  (p0_Identifier.(sn.HeatingSystem_Functioning_Room_valvePos)) =
  CLOSED
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier ->
     HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15)
  (all Identifier_aa: Identifier - p0_Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                                                   (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  {((none -> none).((p0_Identifier ->
                     HeatingSystem_Functioning_Room).(none.(none.(p0_Identifier.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_RoomScope)))}
       )}

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(HeatingSystem in sc0) &&
    !((p0_Identifier -> HeatingSystem_Functioning_Room) in
        sc1) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_pre)
  p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_post))
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat) &
   (s.dsh_conf1))
  !((p0_Identifier.(s.HeatingSystem_Functioning_Room_desiredTemp)).((p0_Identifier.(s.HeatingSystem_Functioning_Room_actualTemp)).lt))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> HeatingSystem_Functioning_RoomScope) in
    (s.dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      ((p0_Identifier ->
          HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat) +
         (p0_Identifier ->
            HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat))) +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat))
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier ->
     HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((p0_Identifier ->
                     HeatingSystem_Functioning_Room).(none.(none.(p0_Identifier.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_RoomScope)))}
       )}

}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(HeatingSystem in sc0) &&
    !((p0_Identifier -> HeatingSystem_Functioning_Room) in
        sc1) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13 [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_pre)
  p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_post))
}

pred HeatingSystem_Functioning_Controller_On_Idle_T9_pre [
	s: one DshSnapshot] {
  some
(HeatingSystem_Functioning_Controller_On_Idle &
   (s.dsh_conf0))
  (some r: Identifier | (r.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                        True)
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !(HeatingSystem_Functioning_ControllerScope in
    (s.dsh_sc_used0))
}


pred HeatingSystem_Functioning_Controller_On_Idle_T9_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (HeatingSystem_Functioning_Controller_On_Idle +
         HeatingSystem_Functioning_Controller_On_Heater_Active)) +
     HeatingSystem_Functioning_Controller_On_Heater_Active)
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.dsh_taken0) =
  HeatingSystem_Functioning_Controller_On_Idle_T9
  (sn.dsh_taken1) = (none -> none)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((none -> none).(HeatingSystem_activate.(HeatingSystem_Functioning_Controller.(none.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              HeatingSystem_activate)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (HeatingSystem_activate +
                 ((s.dsh_events0) :> DshIntEvents)))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              HeatingSystem_activate &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) + HeatingSystem_activate) &&
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) +
                   HeatingSystem_Functioning_ControllerScope) &&
              (sn.dsh_sc_used1) = (s.dsh_sc_used1))}
       )}

}

pred HeatingSystem_Functioning_Controller_On_Idle_T9_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
(HeatingSystem_Functioning_Controller_On_Idle &
   (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue &&
    !(HeatingSystem in sc0) &&
    !(HeatingSystem_Functioning_Controller in sc0) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred HeatingSystem_Functioning_Controller_On_Idle_T9 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.HeatingSystem_Functioning_Controller_On_Idle_T9_pre
  sn.(s.HeatingSystem_Functioning_Controller_On_Idle_T9_post)
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_pre [
	s: one DshSnapshot,
	p0_Identifier: one Identifier] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating) &
   (s.dsh_conf1))
  !((p0_Identifier.(s.HeatingSystem_Functioning_Room_desiredTemp)).((p0_Identifier.(s.HeatingSystem_Functioning_Room_actualTemp)).gt))
  !(HeatingSystemScope in (s.dsh_sc_used0))
  !((p0_Identifier -> HeatingSystem_Functioning_RoomScope) in
    (s.dsh_sc_used1))
}


pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_post [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_conf1) =
  (((s.dsh_conf1) -
      (p0_Identifier ->
         HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating)) +
     (p0_Identifier ->
        HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating))
  (p0_Identifier.(sn.HeatingSystem_Functioning_Room_actualTemp)) =
  ((p0_Identifier.(s.HeatingSystem_Functioning_Room_actualTemp)).temp/next)
  (sn.dsh_taken0) = none
  (sn.dsh_taken1) =
  (p0_Identifier ->
     HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom)
  (all Identifier_aa: Identifier - p0_Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_actualTemp)) =
                                                   (Identifier_aa.(sn.HeatingSystem_Functioning_Room_actualTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_requestHeat)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_requestHeat)))
  (s.HeatingSystem_Functioning_Controller_controllerOn) =
  (sn.HeatingSystem_Functioning_Controller_controllerOn)
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_desiredTemp)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_desiredTemp)))
  (all Identifier_aa: one
  Identifier | (Identifier_aa.(s.HeatingSystem_Functioning_Room_valvePos)) =
                 (Identifier_aa.(sn.HeatingSystem_Functioning_Room_valvePos)))
  {((none -> none).((p0_Identifier ->
                     HeatingSystem_Functioning_Room).(none.(none.(p0_Identifier.(sn.(s._nextIsStable)))))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
       (sn.dsh_sc_used1) = (none -> none) &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))}
       )
  else
    ((sn.dsh_stable).boolean/isFalse &&
       {((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none &&
              ((sn.dsh_events0) :> DshEnvEvents) =
                ((s.dsh_events0) :> DshEnvEvents) &&
              (sn.dsh_sc_used0) = none &&
              ((sn.dsh_events1) :> DshEnvEvents) =
                ((s.dsh_events1) :> DshEnvEvents) &&
              (sn.dsh_sc_used1) = (none -> none))
         else
           ((sn.dsh_sc_used0) = (s.dsh_sc_used0) &&
              (sn.dsh_sc_used1) =
                ((s.dsh_sc_used1) +
                   (p0_Identifier ->
                      HeatingSystem_Functioning_RoomScope)))}
       )}

}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  some
((p0_Identifier ->
    HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating) &
   (sn.dsh_conf1))
  { (s.dsh_stable).boolean/isTrue &&
    !(HeatingSystem in sc0) &&
    !((p0_Identifier -> HeatingSystem_Functioning_Room) in
        sc1) ||
    !((s.dsh_stable).boolean/isTrue) }
}

pred HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier] {
  p0_Identifier.(s.HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_pre)
  p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_post))
}

pred _nextIsStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	p0_Identifier: one Identifier,
	sc0: DshStates,
	genEvs0: DshEvents,
	sc1: DshIds -> DshStates,
	genEvs1: DshIds -> DshEvents] {
  !(genEvs1.(sc1.(genEvs0.(sc0.(sn.(s.HeatingSystem_Functioning_Controller_Off_T8_enabledAfterStep))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(sn.(s.HeatingSystem_Functioning_Controller_On_Heater_Active_T10_enabledAfterStep))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(sn.(s.HeatingSystem_Functioning_Controller_On_Heater_Active_T11_enabledAfterStep))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_enabledAfterStep))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_enabledAfterStep))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_enabledAfterStep))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_enabledAfterStep))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(sn.(s.HeatingSystem_ERROR_T19_enabledAfterStep))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_enabledAfterStep))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_enabledAfterStep)))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(sn.(s.HeatingSystem_Functioning_Controller_On_Idle_T9_enabledAfterStep))))))
  !(genEvs1.(sc1.(genEvs0.(sc0.(p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_enabledAfterStep)))))))
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_stable) = (s.dsh_stable)
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_sc_used0) = (s.dsh_sc_used0)
  (sn.dsh_taken0) = NO_TRANS
  ((sn.dsh_events0) :> DshIntEvents) = none
  (sn.dsh_conf1) = (s.dsh_conf1)
  (sn.dsh_sc_used1) = (s.dsh_sc_used1)
  (sn.dsh_taken1) = (none -> none)
  (sn.HeatingSystem_Functioning_Controller_controllerOn) =
  (s.HeatingSystem_Functioning_Controller_controllerOn)
  (sn.HeatingSystem_Functioning_Room_actualTemp) =
  (s.HeatingSystem_Functioning_Room_actualTemp)
  (sn.HeatingSystem_Functioning_Room_desiredTemp) =
  (s.HeatingSystem_Functioning_Room_desiredTemp)
  (sn.HeatingSystem_Functioning_Room_valvePos) =
  (s.HeatingSystem_Functioning_Room_valvePos)
  (sn.HeatingSystem_Functioning_Room_requestHeat) =
  (s.HeatingSystem_Functioning_Room_requestHeat)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { (some p0_Identifier: one
      Identifier | { sn.(s.HeatingSystem_Functioning_Controller_Off_T8) ||
                       sn.(s.HeatingSystem_Functioning_Controller_On_Heater_Active_T10) ||
                       sn.(s.HeatingSystem_Functioning_Controller_On_Heater_Active_T11) ||
                       sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4) ||
                       sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5) ||
                       sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3) ||
                       p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom)) ||
                       p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12)) ||
                       p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17)) ||
                       sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1) ||
                       p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16)) ||
                       sn.(s.HeatingSystem_ERROR_T19) ||
                       p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18)) ||
                       p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14)) ||
                       p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15)) ||
                       sn.(s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2) ||
                       p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15)) ||
                       p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13)) ||
                       sn.(s.HeatingSystem_Functioning_Controller_On_Idle_T9) ||
                       p0_Identifier.(sn.(s.HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom)) }) ||
    !((some p0_Identifier: one
         Identifier | { s.HeatingSystem_Functioning_Controller_Off_T8_pre ||
                          s.HeatingSystem_Functioning_Controller_On_Heater_Active_T10_pre ||
                          s.HeatingSystem_Functioning_Controller_On_Heater_Active_T11_pre ||
                          s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T4_pre ||
                          s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Running_T5_pre ||
                          s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T3_pre ||
                          p0_Identifier.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_coolRoom_pre) ||
                          p0_Identifier.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Idle_No_Heat_T12_pre) ||
                          p0_Identifier.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T17_pre) ||
                          s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Off_T1_pre ||
                          p0_Identifier.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T16_pre) ||
                          s.HeatingSystem_ERROR_T19_pre ||
                          p0_Identifier.(s.HeatingSystem_Functioning_Room_Heat_Requested_Wait_For_Cool_T18_pre) ||
                          p0_Identifier.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T14_pre) ||
                          p0_Identifier.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T15_pre) ||
                          s.HeatingSystem_Functioning_Furnace_Furnace_Normal_Furnace_Activating_T2_pre ||
                          p0_Identifier.(s.HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_T15_pre) ||
                          p0_Identifier.(s.HeatingSystem_Functioning_Room_No_Heat_Request_Wait_For_Heat_T13_pre) ||
                          s.HeatingSystem_Functioning_Controller_On_Idle_T9_pre ||
                          p0_Identifier.(s.HeatingSystem_Functioning_Room_Heat_Requested_Idle_Heating_heatRoom_pre) })) &&
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
                   (s.dsh_events0) = (sn.dsh_events0) &&
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

/*
default state Idle {
	trans T9 {
		when heatRequested 
		send activate
		goto Heater_Active
	}
*/

fun is_a_next_state: set DshSnapshot {
    ex[ {s: DshSnapshot | boolean/isTrue[boolean/True] } ]
}

one sig R extends Identifier {}

pred ef_trans_T9 {
    ctl_mc[
        imp_ctl[and_ctl[{ s : DshSnapshot | 
                HeatingSystem_Functioning_Controller_On_Idle in s.dsh_conf0 and
                (R.(s.HeatingSystem_Functioning_Room_requestHeat) = True)
                 },
                is_a_next_state ],
                ef[{s: DshSnapshot | HeatingSystem_Functioning_Controller_On_Idle_T9 in s.dsh_taken0 }]
            ]
    ]
}

check {
    ef_trans_T9
}
for 
exactly 18 DshSnapshot,
exactly 6 Identifier,
exactly 6 Temp    
expect 0



/*

dashcli -t -m tcmc heating-system.dsh
cat heating-system-tcmc.als heating-system-tcmc-trans-ef-T9.ver > heating-system-tcmc-trans-ef-T9.als
time dashcli heating-system-tcmc-trans-ef-T9.als

*/