/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-13 16:48:53
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/*******************************************************************************
 * Title: FDG_model_logic.dsh
 * Authors: Jose Serna - jserna@uwaterloo.ca
 * Created: 2018-06-20
 * Last modified: 
 * 2023-06-07 Nancy Day small changes for new dash
 *
 * Notes: Dash model of the Mode Logic of a single sie of the Flight Guidance 
 *        System (FGS) described in "Formal Methods Case Studies for DO-333"
 *
 ******************************************************************************/
open util/boolean

/**
 *The model contains 24 boolean inputs and 29 boolean outputs
 */
abstract sig DshStates {}
abstract sig FlightModes extends DshStates {} 
abstract sig FlightModes_FD extends FlightModes {} 
one sig FlightModes_FD_OFF extends FlightModes_FD {} 
one sig FlightModes_FD_ON extends FlightModes_FD {} 
abstract sig FlightModes_ANNUNCIATIONS extends FlightModes {} 
one sig FlightModes_ANNUNCIATIONS_OFF extends FlightModes_ANNUNCIATIONS {} 
one sig FlightModes_ANNUNCIATIONS_ON extends FlightModes_ANNUNCIATIONS {} 
abstract sig FlightModes_LATERAL extends FlightModes {} 
abstract sig FlightModes_LATERAL_HDG extends FlightModes_LATERAL {} 
one sig FlightModes_LATERAL_HDG_CLEARED extends FlightModes_LATERAL_HDG {} 
abstract sig FlightModes_LATERAL_HDG_SELECTED extends FlightModes_LATERAL_HDG {} 
one sig FlightModes_LATERAL_HDG_SELECTED_ACTIVE extends FlightModes_LATERAL_HDG_SELECTED {} 
abstract sig FlightModes_LATERAL_NAV extends FlightModes_LATERAL {} 
one sig FlightModes_LATERAL_NAV_CLEARED extends FlightModes_LATERAL_NAV {} 
abstract sig FlightModes_LATERAL_NAV_SELECTED extends FlightModes_LATERAL_NAV {} 
one sig FlightModes_LATERAL_NAV_SELECTED_ARMED extends FlightModes_LATERAL_NAV_SELECTED {} 
one sig FlightModes_LATERAL_NAV_SELECTED_ACTIVE extends FlightModes_LATERAL_NAV_SELECTED {} 
abstract sig FlightModes_LATERAL_LAPPR extends FlightModes_LATERAL {} 
one sig FlightModes_LATERAL_LAPPR_CLEARED extends FlightModes_LATERAL_LAPPR {} 
abstract sig FlightModes_LATERAL_LAPPR_SELECTED extends FlightModes_LATERAL_LAPPR {} 
one sig FlightModes_LATERAL_LAPPR_SELECTED_ARMED extends FlightModes_LATERAL_LAPPR_SELECTED {} 
one sig FlightModes_LATERAL_LAPPR_SELECTED_ACTIVE extends FlightModes_LATERAL_LAPPR_SELECTED {} 
abstract sig FlightModes_LATERAL_LGA extends FlightModes_LATERAL {} 
one sig FlightModes_LATERAL_LGA_CLEARED extends FlightModes_LATERAL_LGA {} 
abstract sig FlightModes_LATERAL_LGA_SELECTED extends FlightModes_LATERAL_LGA {} 
one sig FlightModes_LATERAL_LGA_SELECTED_ACTIVE extends FlightModes_LATERAL_LGA_SELECTED {} 
abstract sig FlightModes_LATERAL_ROLL extends FlightModes_LATERAL {} 
one sig FlightModes_LATERAL_ROLL_CLEARED extends FlightModes_LATERAL_ROLL {} 
abstract sig FlightModes_LATERAL_ROLL_SELECTED extends FlightModes_LATERAL_ROLL {} 
one sig FlightModes_LATERAL_ROLL_SELECTED_ACTIVE extends FlightModes_LATERAL_ROLL_SELECTED {} 
abstract sig FlightModes_VERTICAL extends FlightModes {} 
abstract sig FlightModes_VERTICAL_VS extends FlightModes_VERTICAL {} 
one sig FlightModes_VERTICAL_VS_CLEARED extends FlightModes_VERTICAL_VS {} 
abstract sig FlightModes_VERTICAL_VS_SELECTED extends FlightModes_VERTICAL_VS {} 
one sig FlightModes_VERTICAL_VS_SELECTED_ACTIVE extends FlightModes_VERTICAL_VS_SELECTED {} 
abstract sig FlightModes_VERTICAL_FLC extends FlightModes_VERTICAL {} 
one sig FlightModes_VERTICAL_FLC_CLEARED extends FlightModes_VERTICAL_FLC {} 
abstract sig FlightModes_VERTICAL_FLC_SELECTED extends FlightModes_VERTICAL_FLC {} 
one sig FlightModes_VERTICAL_FLC_SELECTED_ACTIVE extends FlightModes_VERTICAL_FLC_SELECTED {} 
abstract sig FlightModes_VERTICAL_ALT extends FlightModes_VERTICAL {} 
one sig FlightModes_VERTICAL_ALT_CLEARED extends FlightModes_VERTICAL_ALT {} 
abstract sig FlightModes_VERTICAL_ALT_SELECTED extends FlightModes_VERTICAL_ALT {} 
one sig FlightModes_VERTICAL_ALT_SELECTED_ACTIVE extends FlightModes_VERTICAL_ALT_SELECTED {} 
abstract sig FlightModes_VERTICAL_ALTSEL extends FlightModes_VERTICAL {} 
one sig FlightModes_VERTICAL_ALTSEL_CLEARED extends FlightModes_VERTICAL_ALTSEL {} 
abstract sig FlightModes_VERTICAL_ALTSEL_SELECTED extends FlightModes_VERTICAL_ALTSEL {} 
one sig FlightModes_VERTICAL_ALTSEL_SELECTED_ARMED extends FlightModes_VERTICAL_ALTSEL_SELECTED {} 
abstract sig FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE extends FlightModes_VERTICAL_ALTSEL_SELECTED {} 
one sig FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE extends FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE {} 
one sig FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK extends FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE {} 
abstract sig FlightModes_VERTICAL_VAPPR extends FlightModes_VERTICAL {} 
one sig FlightModes_VERTICAL_VAPPR_CLEARED extends FlightModes_VERTICAL_VAPPR {} 
abstract sig FlightModes_VERTICAL_VAPPR_SELECTED extends FlightModes_VERTICAL_VAPPR {} 
one sig FlightModes_VERTICAL_VAPPR_SELECTED_ARMED extends FlightModes_VERTICAL_VAPPR_SELECTED {} 
one sig FlightModes_VERTICAL_VAPPR_SELECTED_ACTIVE extends FlightModes_VERTICAL_VAPPR_SELECTED {} 
abstract sig FlightModes_VERTICAL_VGA extends FlightModes_VERTICAL {} 
one sig FlightModes_VERTICAL_VGA_CLEARED extends FlightModes_VERTICAL_VGA {} 
abstract sig FlightModes_VERTICAL_VGA_SELECTED extends FlightModes_VERTICAL_VGA {} 
one sig FlightModes_VERTICAL_VGA_SELECTED_ACTIVE extends FlightModes_VERTICAL_VGA_SELECTED {} 
abstract sig FlightModes_VERTICAL_PITCH extends FlightModes_VERTICAL {} 
one sig FlightModes_VERTICAL_PITCH_CLEARED extends FlightModes_VERTICAL_PITCH {} 
abstract sig FlightModes_VERTICAL_PITCH_SELECTED extends FlightModes_VERTICAL_PITCH {} 
one sig FlightModes_VERTICAL_PITCH_SELECTED_ACTIVE extends FlightModes_VERTICAL_PITCH_SELECTED {} 

abstract sig DshEvents {}
abstract sig DshIntEvents extends DshEvents {} 
one sig FlightModes_LATERAL_New_Lateral_Mode_Activated extends DshIntEvents {} 
one sig FlightModes_VERTICAL_New_Vertical_Mode_Activated extends DshIntEvents {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  dsh_events0: set DshEvents,
  dsh_stable: one boolean/Bool,
  FlightModes_Pilot_Flying_Side: one Bool,
  FlightModes_Pilot_Flying_Transfer: one Bool,
  FlightModes_HDG_Switch_Pressed: one Bool,
  FlightModes_NAV_Switch_Pressed: one Bool,
  FlightModes_GA_Switch_Pressed: one Bool,
  FlightModes_When_AP_Engaged: one Bool,
  FlightModes_FD_Switch_Pressed: one Bool,
  FlightModes_Overspeed: one Bool,
  FlightModes_VS_Switch_Pressed: one Bool,
  FlightModes_FLC_Switch_Pressed: one Bool,
  FlightModes_ALT_Switch_Pressed: one Bool,
  FlightModes_APPR_Switch_Pressed: one Bool,
  FlightModes_VS_Pitch_Wheel_Rotated: one Bool,
  FlightModes_Selected_NAV_Source_Changed: one Bool,
  FlightModes_Selected_NAV_Frequency_Changed: one Bool,
  FlightModes_Is_AP_Engaged: one Bool,
  FlightModes_Is_Offside_FD_On: one Bool,
  FlightModes_LAPPR_Capture_Condition_Met: one Bool,
  FlightModes_SYNC_Switch_Pressed: one Bool,
  FlightModes_NAV_Capture_Condition_Met: one Bool,
  FlightModes_ALTSEL_Target_Changed: one Bool,
  FlightModes_ALTSEL_Capture_Condition_Met: one Bool,
  FlightModes_ALTSEL_Track_Condition_Met: one Bool,
  FlightModes_VAPPR_Capture_Condition_Met: one Bool,
  FlightModes_FD_On: one Bool,
  FlightModes_Modes_On: one Bool,
  FlightModes_HDG_Selected: one Bool,
  FlightModes_HDG_Active: one Bool,
  FlightModes_NAV_Selected: one Bool,
  FlightModes_NAV_Active: one Bool,
  FlightModes_VS_Active: one Bool,
  FlightModes_LAPPR_Selected: one Bool,
  FlightModes_LAPPR_Active: one Bool,
  FlightModes_LGA_Selected: one Bool,
  FlightModes_LGA_Active: one Bool,
  FlightModes_ROLL_Active: one Bool,
  FlightModes_ROLL_Selected: one Bool,
  FlightModes_VS_Selected: one Bool,
  FlightModes_FLC_Selected: one Bool,
  FlightModes_FLC_Active: one Bool,
  FlightModes_ALT_Active: one Bool,
  FlightModes_ALTSEL_Active: one Bool,
  FlightModes_ALT_Selected: one Bool,
  FlightModes_ALTSEL_Track: one Bool,
  FlightModes_ALTSEL_Selected: one Bool,
  FlightModes_PITCH_Selected: one Bool,
  FlightModes_VAPPR_Selected: one Bool,
  FlightModes_VAPPR_Active: one Bool,
  FlightModes_VGA_Selected: one Bool,
  FlightModes_VGA_Active: one Bool,
  FlightModes_PITCH_Active: one Bool,
  FlightModes_Independent_Mode: one Bool,
  FlightModes_Active_Side: one Bool
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) =
  (((((((((((((FlightModes_FD_OFF +
                 FlightModes_ANNUNCIATIONS_OFF) +
                FlightModes_LATERAL_HDG_CLEARED) +
               FlightModes_LATERAL_NAV_CLEARED) +
              FlightModes_LATERAL_LAPPR_CLEARED) +
             FlightModes_LATERAL_LGA_CLEARED) +
            FlightModes_LATERAL_ROLL_SELECTED_ACTIVE) +
           FlightModes_VERTICAL_VS_CLEARED) +
          FlightModes_VERTICAL_FLC_CLEARED) +
         FlightModes_VERTICAL_ALT_CLEARED) +
        FlightModes_VERTICAL_ALTSEL_CLEARED) +
       FlightModes_VERTICAL_VAPPR_CLEARED) +
      FlightModes_VERTICAL_VGA_CLEARED) +
     FlightModes_VERTICAL_PITCH_SELECTED_ACTIVE) and
  (s.FlightModes_FD_On) = False and
  (s.FlightModes_Modes_On) = False and
  (s.FlightModes_HDG_Selected) = False and
  (s.FlightModes_HDG_Active) = False and
  (s.FlightModes_NAV_Selected) = False and
  (s.FlightModes_NAV_Active) = False and
  (s.FlightModes_VS_Active) = False and
  (s.FlightModes_LAPPR_Selected) = False and
  (s.FlightModes_LAPPR_Active) = False and
  (s.FlightModes_LGA_Selected) = False and
  (s.FlightModes_LGA_Active) = False and
  (s.FlightModes_ROLL_Active) = True and
  (s.FlightModes_ROLL_Selected) = True and
  (s.FlightModes_VS_Selected) = False and
  (s.FlightModes_FLC_Selected) = False and
  (s.FlightModes_FLC_Active) = False and
  (s.FlightModes_ALT_Active) = False and
  (s.FlightModes_ALTSEL_Active) = False and
  (s.FlightModes_ALT_Selected) = False and
  (s.FlightModes_ALTSEL_Track) = False and
  (s.FlightModes_ALTSEL_Selected) = False and
  (s.FlightModes_PITCH_Selected) = True and
  (s.FlightModes_VAPPR_Selected) = False and
  (s.FlightModes_VAPPR_Active) = False and
  (s.FlightModes_VGA_Selected) = False and
  (s.FlightModes_VGA_Active) = False and
  (s.FlightModes_PITCH_Active) = True and
  (s.FlightModes_Independent_Mode) = False and
  (s.FlightModes_Active_Side) = False
  (s.dsh_stable).boolean/isTrue
}

fact inv {  (all s: one
  DshSnapshot | (s.FlightModes_When_AP_Engaged) =
                  (s.FlightModes_Is_AP_Engaged))
}

pred FlightModes_LATERAL_LAPPR_Capture_pre [
	s: one DshSnapshot] {
  some
(FlightModes_LATERAL_LAPPR_SELECTED_ARMED & (s.dsh_conf0))
  (s.FlightModes_LAPPR_Capture_Condition_Met) = True
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_LAPPR in (s.dsh_sc_used0))
  !(s.FlightModes_LATERAL_LAPPR_Clear_pre)
}


pred FlightModes_LATERAL_LAPPR_Capture_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) -
       FlightModes_LATERAL_LAPPR_SELECTED_ARMED) -
      FlightModes_LATERAL_LAPPR_SELECTED_ACTIVE) +
     FlightModes_LATERAL_LAPPR_SELECTED_ACTIVE)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (FlightModes_LATERAL_New_Lateral_Mode_Activated.(FlightModes_LATERAL_LAPPR.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_LATERAL_New_Lateral_Mode_Activated)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (FlightModes_LATERAL_New_Lateral_Mode_Activated +
                 ((s.dsh_events0) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_LATERAL_New_Lateral_Mode_Activated and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) +
                 FlightModes_LATERAL_New_Lateral_Mode_Activated) and
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) +
                   FlightModes_LATERAL_LAPPR))
       )

}

pred FlightModes_LATERAL_LAPPR_Capture_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_LATERAL_LAPPR_SELECTED_ARMED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_LATERAL in dsh_scp0) and
    !(FlightModes_LATERAL_LAPPR in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_LATERAL_LAPPR_Capture [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_LAPPR_Capture_pre
  sn.(s.FlightModes_LATERAL_LAPPR_Capture_post)
}

pred FlightModes_VERTICAL_ALT_NewVerticalModeActivated_pre [
	s: one DshSnapshot] {
  some
(FlightModes_VERTICAL_ALT_SELECTED_ACTIVE & (s.dsh_conf0))
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_ALT in (s.dsh_sc_used0))
  FlightModes_VERTICAL_New_Vertical_Mode_Activated in
  (s.dsh_events0)
  !(s.FlightModes_VERTICAL_ALT_Clear_pre)
}


pred FlightModes_VERTICAL_ALT_NewVerticalModeActivated_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_ALT_CLEARED) -
      FlightModes_VERTICAL_ALT_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_ALT_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_ALT.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_ALT))
       )

}

pred FlightModes_VERTICAL_ALT_NewVerticalModeActivated_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_VERTICAL_ALT_SELECTED_ACTIVE & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) and
  FlightModes_VERTICAL_New_Vertical_Mode_Activated in
    ((s.dsh_events0) + dsh_genEvs0)
}

pred FlightModes_VERTICAL_ALT_NewVerticalModeActivated [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_ALT_NewVerticalModeActivated_pre
  sn.(s.FlightModes_VERTICAL_ALT_NewVerticalModeActivated_post)
}

pred FlightModes_LATERAL_NAV_Select_pre [
	s: one DshSnapshot] {
  some (FlightModes_LATERAL_NAV_CLEARED & (s.dsh_conf0))
  (s.FlightModes_NAV_Switch_Pressed) = True
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_NAV in (s.dsh_sc_used0))
}


pred FlightModes_LATERAL_NAV_Select_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - FlightModes_LATERAL_NAV_CLEARED) -
       FlightModes_LATERAL_NAV_SELECTED_ARMED) -
      FlightModes_LATERAL_NAV_SELECTED_ACTIVE) +
     FlightModes_LATERAL_NAV_SELECTED_ARMED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_LATERAL_NAV.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_LATERAL_NAV))
       )

}

pred FlightModes_LATERAL_NAV_Select_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_LATERAL_NAV_CLEARED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_LATERAL in dsh_scp0) and
    !(FlightModes_LATERAL_NAV in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_LATERAL_NAV_Select [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_NAV_Select_pre
  sn.(s.FlightModes_LATERAL_NAV_Select_post)
}

pred FlightModes_LATERAL_NAV_NewLateralModeActivated_pre [
	s: one DshSnapshot] {
  some
(FlightModes_LATERAL_NAV_SELECTED_ACTIVE & (s.dsh_conf0))
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_NAV in (s.dsh_sc_used0))
  FlightModes_LATERAL_New_Lateral_Mode_Activated in
  (s.dsh_events0)
  !(s.FlightModes_LATERAL_NAV_Clear_pre)
}


pred FlightModes_LATERAL_NAV_NewLateralModeActivated_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - FlightModes_LATERAL_NAV_CLEARED) -
       FlightModes_LATERAL_NAV_SELECTED_ARMED) -
      FlightModes_LATERAL_NAV_SELECTED_ACTIVE) +
     FlightModes_LATERAL_NAV_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_LATERAL_NAV.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_LATERAL_NAV))
       )

}

pred FlightModes_LATERAL_NAV_NewLateralModeActivated_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_LATERAL_NAV_SELECTED_ACTIVE & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) and
  FlightModes_LATERAL_New_Lateral_Mode_Activated in
    ((s.dsh_events0) + dsh_genEvs0)
}

pred FlightModes_LATERAL_NAV_NewLateralModeActivated [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_NAV_NewLateralModeActivated_pre
  sn.(s.FlightModes_LATERAL_NAV_NewLateralModeActivated_post)
}

pred FlightModes_ANNUNCIATIONS_TurnAnnunciationsOn_pre [
	s: one DshSnapshot] {
  some (FlightModes_ANNUNCIATIONS_OFF & (s.dsh_conf0))
  { (s.FlightModes_Is_AP_Engaged) = True or
    (s.FlightModes_Is_Offside_FD_On) = True or
    (s.FlightModes_FD_On) = True }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_ANNUNCIATIONS in (s.dsh_sc_used0))
}


pred FlightModes_ANNUNCIATIONS_TurnAnnunciationsOn_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_ANNUNCIATIONS_OFF) -
      FlightModes_ANNUNCIATIONS_ON) +
     FlightModes_ANNUNCIATIONS_ON)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_ANNUNCIATIONS.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_ANNUNCIATIONS))
       )

}

pred FlightModes_ANNUNCIATIONS_TurnAnnunciationsOn_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_ANNUNCIATIONS_OFF & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_ANNUNCIATIONS in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_ANNUNCIATIONS_TurnAnnunciationsOn [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_ANNUNCIATIONS_TurnAnnunciationsOn_pre
  sn.(s.FlightModes_ANNUNCIATIONS_TurnAnnunciationsOn_post)
}

pred FlightModes_VERTICAL_VAPPR_NewVerticalModeActivated_pre [
	s: one DshSnapshot] {
  some
(FlightModes_VERTICAL_VAPPR_SELECTED_ACTIVE & (s.dsh_conf0))
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_VAPPR in (s.dsh_sc_used0))
  FlightModes_VERTICAL_New_Vertical_Mode_Activated in
  (s.dsh_events0)
  !(s.FlightModes_VERTICAL_VAPPR_Clear_pre)
}


pred FlightModes_VERTICAL_VAPPR_NewVerticalModeActivated_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - FlightModes_VERTICAL_VAPPR_CLEARED) -
       FlightModes_VERTICAL_VAPPR_SELECTED_ARMED) -
      FlightModes_VERTICAL_VAPPR_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_VAPPR_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_VAPPR.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_VAPPR))
       )

}

pred FlightModes_VERTICAL_VAPPR_NewVerticalModeActivated_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_VERTICAL_VAPPR_SELECTED_ACTIVE & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) and
  FlightModes_VERTICAL_New_Vertical_Mode_Activated in
    ((s.dsh_events0) + dsh_genEvs0)
}

pred FlightModes_VERTICAL_VAPPR_NewVerticalModeActivated [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_VAPPR_NewVerticalModeActivated_pre
  sn.(s.FlightModes_VERTICAL_VAPPR_NewVerticalModeActivated_post)
}

pred FlightModes_ANNUNCIATIONS_TurnAnnunciationsOff_pre [
	s: one DshSnapshot] {
  some (FlightModes_ANNUNCIATIONS_ON & (s.dsh_conf0))
  (s.FlightModes_Is_AP_Engaged) = False and
  (s.FlightModes_Is_Offside_FD_On) = False and
  (s.FlightModes_FD_On) = False
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_ANNUNCIATIONS in (s.dsh_sc_used0))
}


pred FlightModes_ANNUNCIATIONS_TurnAnnunciationsOff_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_ANNUNCIATIONS_OFF) -
      FlightModes_ANNUNCIATIONS_ON) +
     FlightModes_ANNUNCIATIONS_OFF)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_ANNUNCIATIONS.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_ANNUNCIATIONS))
       )

}

pred FlightModes_ANNUNCIATIONS_TurnAnnunciationsOff_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_ANNUNCIATIONS_ON & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_ANNUNCIATIONS in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_ANNUNCIATIONS_TurnAnnunciationsOff [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_ANNUNCIATIONS_TurnAnnunciationsOff_pre
  sn.(s.FlightModes_ANNUNCIATIONS_TurnAnnunciationsOff_post)
}

pred FlightModes_LATERAL_HDG_NewLateralModeActivated_pre [
	s: one DshSnapshot] {
  some
(FlightModes_LATERAL_HDG_SELECTED_ACTIVE & (s.dsh_conf0))
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_HDG in (s.dsh_sc_used0))
  FlightModes_LATERAL_New_Lateral_Mode_Activated in
  (s.dsh_events0)
  !(s.FlightModes_LATERAL_HDG_Clear_pre)
}


pred FlightModes_LATERAL_HDG_NewLateralModeActivated_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_LATERAL_HDG_CLEARED) -
      FlightModes_LATERAL_HDG_SELECTED_ACTIVE) +
     FlightModes_LATERAL_HDG_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_LATERAL_HDG.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_LATERAL_HDG))
       )

}

pred FlightModes_LATERAL_HDG_NewLateralModeActivated_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_LATERAL_HDG_SELECTED_ACTIVE & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) and
  FlightModes_LATERAL_New_Lateral_Mode_Activated in
    ((s.dsh_events0) + dsh_genEvs0)
}

pred FlightModes_LATERAL_HDG_NewLateralModeActivated [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_HDG_NewLateralModeActivated_pre
  sn.(s.FlightModes_LATERAL_HDG_NewLateralModeActivated_post)
}

pred FlightModes_LATERAL_LGA_Select_pre [
	s: one DshSnapshot] {
  some (FlightModes_LATERAL_LGA_CLEARED & (s.dsh_conf0))
  (s.FlightModes_GA_Switch_Pressed) = True and
  (s.FlightModes_Overspeed) = False
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_LGA in (s.dsh_sc_used0))
}


pred FlightModes_LATERAL_LGA_Select_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_LATERAL_LGA_CLEARED) -
      FlightModes_LATERAL_LGA_SELECTED_ACTIVE) +
     FlightModes_LATERAL_LGA_SELECTED_ACTIVE)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (FlightModes_LATERAL_New_Lateral_Mode_Activated.(FlightModes_LATERAL_LGA.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_LATERAL_New_Lateral_Mode_Activated)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (FlightModes_LATERAL_New_Lateral_Mode_Activated +
                 ((s.dsh_events0) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_LATERAL_New_Lateral_Mode_Activated and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) +
                 FlightModes_LATERAL_New_Lateral_Mode_Activated) and
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) + FlightModes_LATERAL_LGA))
       )

}

pred FlightModes_LATERAL_LGA_Select_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_LATERAL_LGA_CLEARED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_LATERAL in dsh_scp0) and
    !(FlightModes_LATERAL_LGA in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_LATERAL_LGA_Select [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_LGA_Select_pre
  sn.(s.FlightModes_LATERAL_LGA_Select_post)
}

pred FlightModes_VERTICAL_FLC_Clear_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_FLC_SELECTED & (s.dsh_conf0))
  { (s.FlightModes_FLC_Switch_Pressed) = True and
    (s.FlightModes_Overspeed) = False or
    (s.FlightModes_Overspeed) = False and
      (s.FlightModes_VS_Pitch_Wheel_Rotated) = True or
    (s.FlightModes_Pilot_Flying_Transfer) = True or
    (s.FlightModes_Modes_On) = False }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_FLC in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_FLC_Clear_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_FLC_CLEARED) -
      FlightModes_VERTICAL_FLC_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_FLC_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_FLC.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_FLC))
       )

}

pred FlightModes_VERTICAL_FLC_Clear_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_FLC_SELECTED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_FLC in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_FLC_Clear [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_FLC_Clear_pre
  sn.(s.FlightModes_VERTICAL_FLC_Clear_post)
}

pred FlightModes_LATERAL_LGA_Clear_pre [
	s: one DshSnapshot] {
  some (FlightModes_LATERAL_LGA_SELECTED & (s.dsh_conf0))
  { (s.FlightModes_When_AP_Engaged) = True or
    (s.FlightModes_SYNC_Switch_Pressed) = True or
    (s.FlightModes_VGA_Active) = False or
    (s.FlightModes_Pilot_Flying_Transfer) = True or
    (s.FlightModes_Modes_On) = False }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_LGA in (s.dsh_sc_used0))
}


pred FlightModes_LATERAL_LGA_Clear_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_LATERAL_LGA_CLEARED) -
      FlightModes_LATERAL_LGA_SELECTED_ACTIVE) +
     FlightModes_LATERAL_LGA_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_LATERAL_LGA.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_LATERAL_LGA))
       )

}

pred FlightModes_LATERAL_LGA_Clear_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_LATERAL_LGA_SELECTED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_LATERAL in dsh_scp0) and
    !(FlightModes_LATERAL_LGA in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_LATERAL_LGA_Clear [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_LGA_Clear_pre
  sn.(s.FlightModes_LATERAL_LGA_Clear_post)
}

pred FlightModes_LATERAL_NAV_Clear_pre [
	s: one DshSnapshot] {
  some (FlightModes_LATERAL_NAV_SELECTED & (s.dsh_conf0))
  { (s.FlightModes_NAV_Switch_Pressed) = True or
    (s.FlightModes_Selected_NAV_Source_Changed) = True or
    (s.FlightModes_Selected_NAV_Frequency_Changed) = True or
    (s.FlightModes_Pilot_Flying_Transfer) = True or
    (s.FlightModes_Modes_On) = False }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_NAV in (s.dsh_sc_used0))
}


pred FlightModes_LATERAL_NAV_Clear_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - FlightModes_LATERAL_NAV_CLEARED) -
       FlightModes_LATERAL_NAV_SELECTED_ARMED) -
      FlightModes_LATERAL_NAV_SELECTED_ACTIVE) +
     FlightModes_LATERAL_NAV_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_LATERAL_NAV.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_LATERAL_NAV))
       )

}

pred FlightModes_LATERAL_NAV_Clear_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_LATERAL_NAV_SELECTED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_LATERAL in dsh_scp0) and
    !(FlightModes_LATERAL_NAV in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_LATERAL_NAV_Clear [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_NAV_Clear_pre
  sn.(s.FlightModes_LATERAL_NAV_Clear_post)
}

pred FlightModes_VERTICAL_PITCH_Select_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_PITCH_CLEARED & (s.dsh_conf0))
  !({ (s.FlightModes_VS_Active) = True or
      (s.FlightModes_FLC_Active) = True or
      (s.FlightModes_ALT_Active) = True or
      (s.FlightModes_ALTSEL_Active) = True or
      (s.FlightModes_VAPPR_Active) = True or
      (s.FlightModes_VGA_Active) = True })
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_PITCH in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_PITCH_Select_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_PITCH_CLEARED) -
      FlightModes_VERTICAL_PITCH_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_PITCH_SELECTED_ACTIVE)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_PITCH.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_PITCH))
       )

}

pred FlightModes_VERTICAL_PITCH_Select_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_PITCH_CLEARED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_PITCH in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_PITCH_Select [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_PITCH_Select_pre
  sn.(s.FlightModes_VERTICAL_PITCH_Select_post)
}

pred FlightModes_VERTICAL_ALTSEL_Select_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_ALTSEL_CLEARED & (s.dsh_conf0))
  (s.FlightModes_VAPPR_Active) = False and
  (s.FlightModes_VGA_Active) = False and
  (s.FlightModes_ALT_Active) = False
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_ALTSEL in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_ALTSEL_Select_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - FlightModes_VERTICAL_ALTSEL_CLEARED) -
        FlightModes_VERTICAL_ALTSEL_SELECTED_ARMED) -
       FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE) -
      FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK) +
     FlightModes_VERTICAL_ALTSEL_SELECTED_ARMED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_ALTSEL.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) +
                 FlightModes_VERTICAL_ALTSEL))
       )

}

pred FlightModes_VERTICAL_ALTSEL_Select_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_ALTSEL_CLEARED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_ALTSEL in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_ALTSEL_Select [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_ALTSEL_Select_pre
  sn.(s.FlightModes_VERTICAL_ALTSEL_Select_post)
}

pred FlightModes_VERTICAL_VAPPR_Capture_pre [
	s: one DshSnapshot] {
  some
(FlightModes_VERTICAL_VAPPR_SELECTED_ARMED & (s.dsh_conf0))
  (s.FlightModes_VAPPR_Capture_Condition_Met) = True and
  (s.FlightModes_LAPPR_Active) = True and
  (s.FlightModes_Overspeed) = False
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_VAPPR in (s.dsh_sc_used0))
  !(s.FlightModes_VERTICAL_VAPPR_Clear_pre)
}


pred FlightModes_VERTICAL_VAPPR_Capture_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) -
       FlightModes_VERTICAL_VAPPR_SELECTED_ARMED) -
      FlightModes_VERTICAL_VAPPR_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_VAPPR_SELECTED_ACTIVE)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (FlightModes_VERTICAL_New_Vertical_Mode_Activated.(FlightModes_VERTICAL_VAPPR.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_VERTICAL_New_Vertical_Mode_Activated)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (FlightModes_VERTICAL_New_Vertical_Mode_Activated +
                 ((s.dsh_events0) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_VERTICAL_New_Vertical_Mode_Activated and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) +
                 FlightModes_VERTICAL_New_Vertical_Mode_Activated) and
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) +
                   FlightModes_VERTICAL_VAPPR))
       )

}

pred FlightModes_VERTICAL_VAPPR_Capture_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_VERTICAL_VAPPR_SELECTED_ARMED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_VAPPR in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_VAPPR_Capture [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_VAPPR_Capture_pre
  sn.(s.FlightModes_VERTICAL_VAPPR_Capture_post)
}

pred FlightModes_VERTICAL_VAPPR_Select_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_VAPPR_CLEARED & (s.dsh_conf0))
  (s.FlightModes_APPR_Switch_Pressed) = True
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_VAPPR in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_VAPPR_Select_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - FlightModes_VERTICAL_VAPPR_CLEARED) -
       FlightModes_VERTICAL_VAPPR_SELECTED_ARMED) -
      FlightModes_VERTICAL_VAPPR_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_VAPPR_SELECTED_ARMED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_VAPPR.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_VAPPR))
       )

}

pred FlightModes_VERTICAL_VAPPR_Select_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_VAPPR_CLEARED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_VAPPR in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_VAPPR_Select [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_VAPPR_Select_pre
  sn.(s.FlightModes_VERTICAL_VAPPR_Select_post)
}

pred FlightModes_VERTICAL_ALT_Clear_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_ALT_SELECTED & (s.dsh_conf0))
  { (s.FlightModes_ALT_Switch_Pressed) = True or
    (s.FlightModes_VS_Pitch_Wheel_Rotated) = True or
    (s.FlightModes_Pilot_Flying_Transfer) = True or
    (s.FlightModes_Modes_On) = False }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_ALT in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_ALT_Clear_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_ALT_CLEARED) -
      FlightModes_VERTICAL_ALT_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_ALT_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_ALT.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_ALT))
       )

}

pred FlightModes_VERTICAL_ALT_Clear_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_ALT_SELECTED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_ALT in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_ALT_Clear [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_ALT_Clear_pre
  sn.(s.FlightModes_VERTICAL_ALT_Clear_post)
}

pred FlightModes_VERTICAL_ALTSEL_Clear_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_ALTSEL_SELECTED & (s.dsh_conf0))
  { (s.FlightModes_VAPPR_Active) = True or
    (s.FlightModes_VGA_Active) = True or
    (s.FlightModes_ALT_Active) = True or
    (s.FlightModes_Modes_On) = False }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_ALTSEL in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_ALTSEL_Clear_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - FlightModes_VERTICAL_ALTSEL_CLEARED) -
        FlightModes_VERTICAL_ALTSEL_SELECTED_ARMED) -
       FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE) -
      FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK) +
     FlightModes_VERTICAL_ALTSEL_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_ALTSEL.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) +
                 FlightModes_VERTICAL_ALTSEL))
       )

}

pred FlightModes_VERTICAL_ALTSEL_Clear_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_ALTSEL_SELECTED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_ALTSEL in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_ALTSEL_Clear [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_ALTSEL_Clear_pre
  sn.(s.FlightModes_VERTICAL_ALTSEL_Clear_post)
}

pred FlightModes_VERTICAL_VGA_Clear_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_VGA_SELECTED & (s.dsh_conf0))
  { (s.FlightModes_When_AP_Engaged) = True or
    (s.FlightModes_SYNC_Switch_Pressed) = True or
    (s.FlightModes_VS_Pitch_Wheel_Rotated) = True or
    (s.FlightModes_Pilot_Flying_Transfer) = True or
    (s.FlightModes_Modes_On) = False }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_VGA in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_VGA_Clear_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_VGA_CLEARED) -
      FlightModes_VERTICAL_VGA_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_VGA_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_VGA.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_VGA))
       )

}

pred FlightModes_VERTICAL_VGA_Clear_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_VGA_SELECTED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_VGA in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_VGA_Clear [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_VGA_Clear_pre
  sn.(s.FlightModes_VERTICAL_VGA_Clear_post)
}

pred FlightModes_FD_TurnFDOff_pre [
	s: one DshSnapshot] {
  some (FlightModes_FD_ON & (s.dsh_conf0))
  (s.FlightModes_FD_Switch_Pressed) = True and
  (s.FlightModes_Overspeed) = False
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_FD in (s.dsh_sc_used0))
}


pred FlightModes_FD_TurnFDOff_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_FD_OFF) - FlightModes_FD_ON) +
     FlightModes_FD_OFF)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_FD.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_FD))
       )

}

pred FlightModes_FD_TurnFDOff_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_FD_ON & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_FD in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_FD_TurnFDOff [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_FD_TurnFDOff_pre
  sn.(s.FlightModes_FD_TurnFDOff_post)
}

pred FlightModes_LATERAL_ROLL_Clear_pre [
	s: one DshSnapshot] {
  some
(FlightModes_LATERAL_ROLL_SELECTED_ACTIVE & (s.dsh_conf0))
  { (s.FlightModes_HDG_Active) = True or
    (s.FlightModes_NAV_Active) = True or
    (s.FlightModes_LAPPR_Active) = True or
    (s.FlightModes_LGA_Active) = True }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_ROLL in (s.dsh_sc_used0))
}


pred FlightModes_LATERAL_ROLL_Clear_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_LATERAL_ROLL_CLEARED) -
      FlightModes_LATERAL_ROLL_SELECTED_ACTIVE) +
     FlightModes_LATERAL_ROLL_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_LATERAL_ROLL.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_LATERAL_ROLL))
       )

}

pred FlightModes_LATERAL_ROLL_Clear_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_LATERAL_ROLL_SELECTED_ACTIVE & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_LATERAL in dsh_scp0) and
    !(FlightModes_LATERAL_ROLL in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_LATERAL_ROLL_Clear [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_ROLL_Clear_pre
  sn.(s.FlightModes_LATERAL_ROLL_Clear_post)
}

pred FlightModes_FD_TurnFDOn_pre [
	s: one DshSnapshot] {
  some (FlightModes_FD_OFF & (s.dsh_conf0))
  { (s.FlightModes_FD_Switch_Pressed) = True or
    (s.FlightModes_When_AP_Engaged) = True or
    (s.FlightModes_Overspeed) = True or
    (s.FlightModes_HDG_Switch_Pressed) = True or
    (s.FlightModes_NAV_Switch_Pressed) = True or
    (s.FlightModes_APPR_Switch_Pressed) = True or
    (s.FlightModes_GA_Switch_Pressed) = True or
    (s.FlightModes_VS_Switch_Pressed) = True or
    (s.FlightModes_FLC_Switch_Pressed) = True or
    (s.FlightModes_ALT_Switch_Pressed) = True or
    (s.FlightModes_APPR_Switch_Pressed) = True or
    (s.FlightModes_GA_Switch_Pressed) = True or
    (s.FlightModes_VS_Pitch_Wheel_Rotated) = True and
      (s.FlightModes_VS_Active) = False and
      (s.FlightModes_VAPPR_Active) = False and
      (s.FlightModes_Overspeed) = False or
    (s.FlightModes_Pilot_Flying_Transfer) = True and
      (s.FlightModes_Pilot_Flying_Side) = True and
      (s.FlightModes_Modes_On) = True }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_FD in (s.dsh_sc_used0))
}


pred FlightModes_FD_TurnFDOn_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_FD_OFF) - FlightModes_FD_ON) +
     FlightModes_FD_ON)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_FD.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_FD))
       )

}

pred FlightModes_FD_TurnFDOn_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_FD_OFF & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_FD in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_FD_TurnFDOn [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_FD_TurnFDOn_pre
  sn.(s.FlightModes_FD_TurnFDOn_post)
}

pred FlightModes_LATERAL_LAPPR_Clear_pre [
	s: one DshSnapshot] {
  some (FlightModes_LATERAL_LAPPR_SELECTED & (s.dsh_conf0))
  { (s.FlightModes_APPR_Switch_Pressed) = True or
    (s.FlightModes_Selected_NAV_Source_Changed) = True or
    (s.FlightModes_Selected_NAV_Frequency_Changed) = True or
    (s.FlightModes_Pilot_Flying_Transfer) = True or
    (s.FlightModes_Modes_On) = False }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_LAPPR in (s.dsh_sc_used0))
}


pred FlightModes_LATERAL_LAPPR_Clear_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - FlightModes_LATERAL_LAPPR_CLEARED) -
       FlightModes_LATERAL_LAPPR_SELECTED_ARMED) -
      FlightModes_LATERAL_LAPPR_SELECTED_ACTIVE) +
     FlightModes_LATERAL_LAPPR_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_LATERAL_LAPPR.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_LATERAL_LAPPR))
       )

}

pred FlightModes_LATERAL_LAPPR_Clear_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_LATERAL_LAPPR_SELECTED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_LATERAL in dsh_scp0) and
    !(FlightModes_LATERAL_LAPPR in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_LATERAL_LAPPR_Clear [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_LAPPR_Clear_pre
  sn.(s.FlightModes_LATERAL_LAPPR_Clear_post)
}

pred FlightModes_VERTICAL_ALTSEL_Capture_pre [
	s: one DshSnapshot] {
  some
(FlightModes_VERTICAL_ALTSEL_SELECTED_ARMED & (s.dsh_conf0))
  (s.FlightModes_ALTSEL_Capture_Condition_Met) = True
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_ALTSEL in (s.dsh_sc_used0))
  !(s.FlightModes_VERTICAL_ALTSEL_Clear_pre)
}


pred FlightModes_VERTICAL_ALTSEL_Capture_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) -
        FlightModes_VERTICAL_ALTSEL_SELECTED_ARMED) -
       FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE) -
      FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK) +
     FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (FlightModes_VERTICAL_New_Vertical_Mode_Activated.(FlightModes_VERTICAL_ALTSEL.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_VERTICAL_New_Vertical_Mode_Activated)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (FlightModes_VERTICAL_New_Vertical_Mode_Activated +
                 ((s.dsh_events0) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_VERTICAL_New_Vertical_Mode_Activated and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) +
                 FlightModes_VERTICAL_New_Vertical_Mode_Activated) and
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) +
                   FlightModes_VERTICAL_ALTSEL))
       )

}

pred FlightModes_VERTICAL_ALTSEL_Capture_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_VERTICAL_ALTSEL_SELECTED_ARMED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_ALTSEL in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_ALTSEL_Capture [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_ALTSEL_Capture_pre
  sn.(s.FlightModes_VERTICAL_ALTSEL_Capture_post)
}

pred FlightModes_VERTICAL_VAPPR_Clear_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_VAPPR_SELECTED & (s.dsh_conf0))
  { (s.FlightModes_APPR_Switch_Pressed) = True or
    (s.FlightModes_LAPPR_Selected) = False or
    (s.FlightModes_Selected_NAV_Source_Changed) = True or
    (s.FlightModes_Selected_NAV_Frequency_Changed) = True or
    (s.FlightModes_Pilot_Flying_Transfer) = True or
    (s.FlightModes_Modes_On) = False }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_VAPPR in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_VAPPR_Clear_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - FlightModes_VERTICAL_VAPPR_CLEARED) -
       FlightModes_VERTICAL_VAPPR_SELECTED_ARMED) -
      FlightModes_VERTICAL_VAPPR_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_VAPPR_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_VAPPR.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_VAPPR))
       )

}

pred FlightModes_VERTICAL_VAPPR_Clear_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_VAPPR_SELECTED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_VAPPR in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_VAPPR_Clear [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_VAPPR_Clear_pre
  sn.(s.FlightModes_VERTICAL_VAPPR_Clear_post)
}

pred FlightModes_LATERAL_LGA_NewLateralModeActivated_pre [
	s: one DshSnapshot] {
  some
(FlightModes_LATERAL_LGA_SELECTED_ACTIVE & (s.dsh_conf0))
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_LGA in (s.dsh_sc_used0))
  FlightModes_LATERAL_New_Lateral_Mode_Activated in
  (s.dsh_events0)
  !(s.FlightModes_LATERAL_LGA_Clear_pre)
}


pred FlightModes_LATERAL_LGA_NewLateralModeActivated_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_LATERAL_LGA_CLEARED) -
      FlightModes_LATERAL_LGA_SELECTED_ACTIVE) +
     FlightModes_LATERAL_LGA_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_LATERAL_LGA.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_LATERAL_LGA))
       )

}

pred FlightModes_LATERAL_LGA_NewLateralModeActivated_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_LATERAL_LGA_SELECTED_ACTIVE & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) and
  FlightModes_LATERAL_New_Lateral_Mode_Activated in
    ((s.dsh_events0) + dsh_genEvs0)
}

pred FlightModes_LATERAL_LGA_NewLateralModeActivated [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_LGA_NewLateralModeActivated_pre
  sn.(s.FlightModes_LATERAL_LGA_NewLateralModeActivated_post)
}

pred FlightModes_LATERAL_HDG_Select_pre [
	s: one DshSnapshot] {
  some (FlightModes_LATERAL_HDG_CLEARED & (s.dsh_conf0))
  (s.FlightModes_HDG_Switch_Pressed) = True
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_HDG in (s.dsh_sc_used0))
}


pred FlightModes_LATERAL_HDG_Select_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_LATERAL_HDG_CLEARED) -
      FlightModes_LATERAL_HDG_SELECTED_ACTIVE) +
     FlightModes_LATERAL_HDG_SELECTED_ACTIVE)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (FlightModes_LATERAL_New_Lateral_Mode_Activated.(FlightModes_LATERAL_HDG.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_LATERAL_New_Lateral_Mode_Activated)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (FlightModes_LATERAL_New_Lateral_Mode_Activated +
                 ((s.dsh_events0) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_LATERAL_New_Lateral_Mode_Activated and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) +
                 FlightModes_LATERAL_New_Lateral_Mode_Activated) and
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) + FlightModes_LATERAL_HDG))
       )

}

pred FlightModes_LATERAL_HDG_Select_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_LATERAL_HDG_CLEARED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_LATERAL in dsh_scp0) and
    !(FlightModes_LATERAL_HDG in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_LATERAL_HDG_Select [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_HDG_Select_pre
  sn.(s.FlightModes_LATERAL_HDG_Select_post)
}

pred FlightModes_VERTICAL_VS_Select_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_VS_CLEARED & (s.dsh_conf0))
  (s.FlightModes_VS_Switch_Pressed) = True and
  (s.FlightModes_Overspeed) = False and
  (s.FlightModes_VAPPR_Active) = False
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_VS in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_VS_Select_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_VS_CLEARED) -
      FlightModes_VERTICAL_VS_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_VS_SELECTED_ACTIVE)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (FlightModes_VERTICAL_New_Vertical_Mode_Activated.(FlightModes_VERTICAL_VS.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_VERTICAL_New_Vertical_Mode_Activated)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (FlightModes_VERTICAL_New_Vertical_Mode_Activated +
                 ((s.dsh_events0) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_VERTICAL_New_Vertical_Mode_Activated and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) +
                 FlightModes_VERTICAL_New_Vertical_Mode_Activated) and
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) + FlightModes_VERTICAL_VS))
       )

}

pred FlightModes_VERTICAL_VS_Select_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_VS_CLEARED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_VS in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_VS_Select [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_VS_Select_pre
  sn.(s.FlightModes_VERTICAL_VS_Select_post)
}

pred FlightModes_VERTICAL_FLC_Select_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_FLC_CLEARED & (s.dsh_conf0))
  { (s.FlightModes_FLC_Switch_Pressed) = True and
    (s.FlightModes_VAPPR_Active) = False or
    (s.FlightModes_Overspeed) = True and
      (s.FlightModes_ALT_Active) = False and
      (s.FlightModes_ALTSEL_Active) = False }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_FLC in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_FLC_Select_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_FLC_CLEARED) -
      FlightModes_VERTICAL_FLC_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_FLC_SELECTED_ACTIVE)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (FlightModes_VERTICAL_New_Vertical_Mode_Activated.(FlightModes_VERTICAL_FLC.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_VERTICAL_New_Vertical_Mode_Activated)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (FlightModes_VERTICAL_New_Vertical_Mode_Activated +
                 ((s.dsh_events0) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_VERTICAL_New_Vertical_Mode_Activated and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) +
                 FlightModes_VERTICAL_New_Vertical_Mode_Activated) and
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) + FlightModes_VERTICAL_FLC))
       )

}

pred FlightModes_VERTICAL_FLC_Select_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_FLC_CLEARED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_FLC in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_FLC_Select [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_FLC_Select_pre
  sn.(s.FlightModes_VERTICAL_FLC_Select_post)
}

pred FlightModes_LATERAL_NAV_Capture_pre [
	s: one DshSnapshot] {
  some
(FlightModes_LATERAL_NAV_SELECTED_ARMED & (s.dsh_conf0))
  (s.FlightModes_NAV_Capture_Condition_Met) = True
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_NAV in (s.dsh_sc_used0))
  !(s.FlightModes_LATERAL_NAV_Clear_pre)
}


pred FlightModes_LATERAL_NAV_Capture_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_LATERAL_NAV_SELECTED_ARMED) -
      FlightModes_LATERAL_NAV_SELECTED_ACTIVE) +
     FlightModes_LATERAL_NAV_SELECTED_ACTIVE)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (FlightModes_LATERAL_New_Lateral_Mode_Activated.(FlightModes_LATERAL_NAV.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_LATERAL_New_Lateral_Mode_Activated)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (FlightModes_LATERAL_New_Lateral_Mode_Activated +
                 ((s.dsh_events0) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_LATERAL_New_Lateral_Mode_Activated and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) +
                 FlightModes_LATERAL_New_Lateral_Mode_Activated) and
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) + FlightModes_LATERAL_NAV))
       )

}

pred FlightModes_LATERAL_NAV_Capture_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_LATERAL_NAV_SELECTED_ARMED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_LATERAL in dsh_scp0) and
    !(FlightModes_LATERAL_NAV in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_LATERAL_NAV_Capture [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_NAV_Capture_pre
  sn.(s.FlightModes_LATERAL_NAV_Capture_post)
}

pred FlightModes_VERTICAL_ALT_Select_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_ALT_CLEARED & (s.dsh_conf0))
  { (s.FlightModes_ALT_Switch_Pressed) = True and
    (s.FlightModes_VAPPR_Active) = False or
    (s.FlightModes_VAPPR_Active) = False and
      (s.FlightModes_ALTSEL_Target_Changed) = True and
      (s.FlightModes_ALTSEL_Track) = True }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_ALT in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_ALT_Select_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_ALT_CLEARED) -
      FlightModes_VERTICAL_ALT_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_ALT_SELECTED_ACTIVE)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (FlightModes_VERTICAL_New_Vertical_Mode_Activated.(FlightModes_VERTICAL_ALT.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_VERTICAL_New_Vertical_Mode_Activated)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (FlightModes_VERTICAL_New_Vertical_Mode_Activated +
                 ((s.dsh_events0) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_VERTICAL_New_Vertical_Mode_Activated and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) +
                 FlightModes_VERTICAL_New_Vertical_Mode_Activated) and
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) + FlightModes_VERTICAL_ALT))
       )

}

pred FlightModes_VERTICAL_ALT_Select_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_ALT_CLEARED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_ALT in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_ALT_Select [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_ALT_Select_pre
  sn.(s.FlightModes_VERTICAL_ALT_Select_post)
}

pred FlightModes_VERTICAL_VGA_NewVerticalModeActivated_pre [
	s: one DshSnapshot] {
  some
(FlightModes_VERTICAL_VGA_SELECTED_ACTIVE & (s.dsh_conf0))
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_VGA in (s.dsh_sc_used0))
  FlightModes_VERTICAL_New_Vertical_Mode_Activated in
  (s.dsh_events0)
  !(s.FlightModes_VERTICAL_VGA_Clear_pre)
}


pred FlightModes_VERTICAL_VGA_NewVerticalModeActivated_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_VGA_CLEARED) -
      FlightModes_VERTICAL_VGA_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_VGA_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_VGA.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_VGA))
       )

}

pred FlightModes_VERTICAL_VGA_NewVerticalModeActivated_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_VERTICAL_VGA_SELECTED_ACTIVE & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) and
  FlightModes_VERTICAL_New_Vertical_Mode_Activated in
    ((s.dsh_events0) + dsh_genEvs0)
}

pred FlightModes_VERTICAL_VGA_NewVerticalModeActivated [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_VGA_NewVerticalModeActivated_pre
  sn.(s.FlightModes_VERTICAL_VGA_NewVerticalModeActivated_post)
}

pred FlightModes_LATERAL_HDG_Clear_pre [
	s: one DshSnapshot] {
  some (FlightModes_LATERAL_HDG_SELECTED & (s.dsh_conf0))
  { (s.FlightModes_HDG_Switch_Pressed) = True or
    (s.FlightModes_Pilot_Flying_Transfer) = True or
    (s.FlightModes_Modes_On) = False }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_HDG in (s.dsh_sc_used0))
}


pred FlightModes_LATERAL_HDG_Clear_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_LATERAL_HDG_CLEARED) -
      FlightModes_LATERAL_HDG_SELECTED_ACTIVE) +
     FlightModes_LATERAL_HDG_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_LATERAL_HDG.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_LATERAL_HDG))
       )

}

pred FlightModes_LATERAL_HDG_Clear_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_LATERAL_HDG_SELECTED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_LATERAL in dsh_scp0) and
    !(FlightModes_LATERAL_HDG in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_LATERAL_HDG_Clear [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_HDG_Clear_pre
  sn.(s.FlightModes_LATERAL_HDG_Clear_post)
}

pred FlightModes_VERTICAL_PITCH_Clear_pre [
	s: one DshSnapshot] {
  some
(FlightModes_VERTICAL_PITCH_SELECTED_ACTIVE & (s.dsh_conf0))
  { (s.FlightModes_VS_Active) = True or
    (s.FlightModes_FLC_Active) = True or
    (s.FlightModes_ALT_Active) = True or
    (s.FlightModes_ALTSEL_Active) = True or
    (s.FlightModes_VAPPR_Active) = True or
    (s.FlightModes_VGA_Active) = True }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_PITCH in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_PITCH_Clear_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_PITCH_CLEARED) -
      FlightModes_VERTICAL_PITCH_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_PITCH_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_PITCH.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_PITCH))
       )

}

pred FlightModes_VERTICAL_PITCH_Clear_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_VERTICAL_PITCH_SELECTED_ACTIVE & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_PITCH in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_PITCH_Clear [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_PITCH_Clear_pre
  sn.(s.FlightModes_VERTICAL_PITCH_Clear_post)
}

pred FlightModes_VERTICAL_VGA_Select_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_VGA_CLEARED & (s.dsh_conf0))
  (s.FlightModes_GA_Switch_Pressed) = True and
  (s.FlightModes_Overspeed) = False
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_VGA in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_VGA_Select_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_VGA_CLEARED) -
      FlightModes_VERTICAL_VGA_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_VGA_SELECTED_ACTIVE)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (FlightModes_VERTICAL_New_Vertical_Mode_Activated.(FlightModes_VERTICAL_VGA.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_VERTICAL_New_Vertical_Mode_Activated)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              (FlightModes_VERTICAL_New_Vertical_Mode_Activated +
                 ((s.dsh_events0) :> DshIntEvents)))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) =
              FlightModes_VERTICAL_New_Vertical_Mode_Activated and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_events0) =
              ((s.dsh_events0) +
                 FlightModes_VERTICAL_New_Vertical_Mode_Activated) and
              (sn.dsh_sc_used0) =
                ((s.dsh_sc_used0) + FlightModes_VERTICAL_VGA))
       )

}

pred FlightModes_VERTICAL_VGA_Select_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_VGA_CLEARED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_VGA in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_VGA_Select [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_VGA_Select_pre
  sn.(s.FlightModes_VERTICAL_VGA_Select_post)
}

pred FlightModes_LATERAL_LAPPR_NewLateralModeActivated_pre [
	s: one DshSnapshot] {
  some
(FlightModes_LATERAL_LAPPR_SELECTED_ACTIVE & (s.dsh_conf0))
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_LAPPR in (s.dsh_sc_used0))
  FlightModes_LATERAL_New_Lateral_Mode_Activated in
  (s.dsh_events0)
  !(s.FlightModes_LATERAL_LAPPR_Clear_pre)
}


pred FlightModes_LATERAL_LAPPR_NewLateralModeActivated_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - FlightModes_LATERAL_LAPPR_CLEARED) -
       FlightModes_LATERAL_LAPPR_SELECTED_ARMED) -
      FlightModes_LATERAL_LAPPR_SELECTED_ACTIVE) +
     FlightModes_LATERAL_LAPPR_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_LATERAL_LAPPR.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_LATERAL_LAPPR))
       )

}

pred FlightModes_LATERAL_LAPPR_NewLateralModeActivated_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_LATERAL_LAPPR_SELECTED_ACTIVE & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) and
  FlightModes_LATERAL_New_Lateral_Mode_Activated in
    ((s.dsh_events0) + dsh_genEvs0)
}

pred FlightModes_LATERAL_LAPPR_NewLateralModeActivated [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_LAPPR_NewLateralModeActivated_pre
  sn.(s.FlightModes_LATERAL_LAPPR_NewLateralModeActivated_post)
}

pred FlightModes_LATERAL_LAPPR_Select_pre [
	s: one DshSnapshot] {
  some (FlightModes_LATERAL_LAPPR_CLEARED & (s.dsh_conf0))
  (s.FlightModes_APPR_Switch_Pressed) = True
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_LAPPR in (s.dsh_sc_used0))
}


pred FlightModes_LATERAL_LAPPR_Select_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((((s.dsh_conf0) - FlightModes_LATERAL_LAPPR_CLEARED) -
       FlightModes_LATERAL_LAPPR_SELECTED_ARMED) -
      FlightModes_LATERAL_LAPPR_SELECTED_ACTIVE) +
     FlightModes_LATERAL_LAPPR_SELECTED_ARMED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_LATERAL_LAPPR.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_LATERAL_LAPPR))
       )

}

pred FlightModes_LATERAL_LAPPR_Select_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_LATERAL_LAPPR_CLEARED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_LATERAL in dsh_scp0) and
    !(FlightModes_LATERAL_LAPPR in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_LATERAL_LAPPR_Select [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_LAPPR_Select_pre
  sn.(s.FlightModes_LATERAL_LAPPR_Select_post)
}

pred FlightModes_LATERAL_ROLL_Select_pre [
	s: one DshSnapshot] {
  some (FlightModes_LATERAL_ROLL_CLEARED & (s.dsh_conf0))
  !({ (s.FlightModes_HDG_Active) = True or
      (s.FlightModes_NAV_Active) = True or
      (s.FlightModes_LAPPR_Active) = True or
      (s.FlightModes_LGA_Active) = True })
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_LATERAL in (s.dsh_sc_used0))
  !(FlightModes_LATERAL_ROLL in (s.dsh_sc_used0))
}


pred FlightModes_LATERAL_ROLL_Select_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_LATERAL_ROLL_CLEARED) -
      FlightModes_LATERAL_ROLL_SELECTED_ACTIVE) +
     FlightModes_LATERAL_ROLL_SELECTED_ACTIVE)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_LATERAL_ROLL.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_LATERAL_ROLL))
       )

}

pred FlightModes_LATERAL_ROLL_Select_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_LATERAL_ROLL_CLEARED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_LATERAL in dsh_scp0) and
    !(FlightModes_LATERAL_ROLL in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_LATERAL_ROLL_Select [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_LATERAL_ROLL_Select_pre
  sn.(s.FlightModes_LATERAL_ROLL_Select_post)
}

pred FlightModes_VERTICAL_ALTSEL_Track_pre [
	s: one DshSnapshot] {
  some
(FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE &
   (s.dsh_conf0))
  (s.FlightModes_ALTSEL_Track_Condition_Met) = True
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_ALTSEL in (s.dsh_sc_used0))
  !(s.FlightModes_VERTICAL_ALTSEL_Clear_pre)
  !(s.FlightModes_VERTICAL_ALTSEL_NewVerticalModeActivated_pre)
}


pred FlightModes_VERTICAL_ALTSEL_Track_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) -
       FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE) -
      FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK) +
     FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_ALTSEL.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) +
                 FlightModes_VERTICAL_ALTSEL))
       )

}

pred FlightModes_VERTICAL_ALTSEL_Track_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE &
   (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_ALTSEL in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_ALTSEL_Track [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_ALTSEL_Track_pre
  sn.(s.FlightModes_VERTICAL_ALTSEL_Track_post)
}

pred FlightModes_VERTICAL_ALTSEL_NewVerticalModeActivated_pre [
	s: one DshSnapshot] {
  some
(FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE & (s.dsh_conf0))
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_ALTSEL in (s.dsh_sc_used0))
  FlightModes_VERTICAL_New_Vertical_Mode_Activated in
  (s.dsh_events0)
  !(s.FlightModes_VERTICAL_ALTSEL_Clear_pre)
}


pred FlightModes_VERTICAL_ALTSEL_NewVerticalModeActivated_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((((s.dsh_conf0) - FlightModes_VERTICAL_ALTSEL_CLEARED) -
        FlightModes_VERTICAL_ALTSEL_SELECTED_ARMED) -
       FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE) -
      FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK) +
     FlightModes_VERTICAL_ALTSEL_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_ALTSEL.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) +
                 FlightModes_VERTICAL_ALTSEL))
       )

}

pred FlightModes_VERTICAL_ALTSEL_NewVerticalModeActivated_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_VERTICAL_ALTSEL_SELECTED_ACTIVE &
   (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) and
  FlightModes_VERTICAL_New_Vertical_Mode_Activated in
    ((s.dsh_events0) + dsh_genEvs0)
}

pred FlightModes_VERTICAL_ALTSEL_NewVerticalModeActivated [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_ALTSEL_NewVerticalModeActivated_pre
  sn.(s.FlightModes_VERTICAL_ALTSEL_NewVerticalModeActivated_post)
}

pred FlightModes_VERTICAL_VS_Clear_pre [
	s: one DshSnapshot] {
  some (FlightModes_VERTICAL_VS_SELECTED & (s.dsh_conf0))
  { (s.FlightModes_VS_Switch_Pressed) = True or
    (s.FlightModes_Pilot_Flying_Transfer) = True or
    (s.FlightModes_Modes_On) = False }
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_VS in (s.dsh_sc_used0))
}


pred FlightModes_VERTICAL_VS_Clear_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_VS_CLEARED) -
      FlightModes_VERTICAL_VS_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_VS_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_VS.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_VS))
       )

}

pred FlightModes_VERTICAL_VS_Clear_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some (FlightModes_VERTICAL_VS_SELECTED & (sn.dsh_conf0))
  { (s.dsh_stable).boolean/isTrue and
    !(FlightModes in dsh_scp0) and
    !(FlightModes_VERTICAL in dsh_scp0) and
    !(FlightModes_VERTICAL_VS in dsh_scp0) or
    !((s.dsh_stable).boolean/isTrue) }
}

pred FlightModes_VERTICAL_VS_Clear [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_VS_Clear_pre
  sn.(s.FlightModes_VERTICAL_VS_Clear_post)
}

pred FlightModes_VERTICAL_FLC_NewVerticalModeActivated_pre [
	s: one DshSnapshot] {
  some
(FlightModes_VERTICAL_FLC_SELECTED_ACTIVE & (s.dsh_conf0))
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_FLC in (s.dsh_sc_used0))
  FlightModes_VERTICAL_New_Vertical_Mode_Activated in
  (s.dsh_events0)
  !(s.FlightModes_VERTICAL_FLC_Clear_pre)
}


pred FlightModes_VERTICAL_FLC_NewVerticalModeActivated_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_FLC_CLEARED) -
      FlightModes_VERTICAL_FLC_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_FLC_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_FLC.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_FLC))
       )

}

pred FlightModes_VERTICAL_FLC_NewVerticalModeActivated_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_VERTICAL_FLC_SELECTED_ACTIVE & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) and
  FlightModes_VERTICAL_New_Vertical_Mode_Activated in
    ((s.dsh_events0) + dsh_genEvs0)
}

pred FlightModes_VERTICAL_FLC_NewVerticalModeActivated [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_FLC_NewVerticalModeActivated_pre
  sn.(s.FlightModes_VERTICAL_FLC_NewVerticalModeActivated_post)
}

pred FlightModes_VERTICAL_VS_NewVerticalModeActivated_pre [
	s: one DshSnapshot] {
  some
(FlightModes_VERTICAL_VS_SELECTED_ACTIVE & (s.dsh_conf0))
  !(FlightModes in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL in (s.dsh_sc_used0))
  !(FlightModes_VERTICAL_VS in (s.dsh_sc_used0))
  FlightModes_VERTICAL_New_Vertical_Mode_Activated in
  (s.dsh_events0)
  !(s.FlightModes_VERTICAL_VS_Clear_pre)
}


pred FlightModes_VERTICAL_VS_NewVerticalModeActivated_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  ((((s.dsh_conf0) - FlightModes_VERTICAL_VS_CLEARED) -
      FlightModes_VERTICAL_VS_SELECTED_ACTIVE) +
     FlightModes_VERTICAL_VS_CLEARED)
  (s.FlightModes_ROLL_Selected) =
  (sn.FlightModes_ROLL_Selected)
  (s.FlightModes_FLC_Selected) = (sn.FlightModes_FLC_Selected)
  (s.FlightModes_ALT_Active) = (sn.FlightModes_ALT_Active)
  (s.FlightModes_PITCH_Selected) =
  (sn.FlightModes_PITCH_Selected)
  (s.FlightModes_HDG_Selected) = (sn.FlightModes_HDG_Selected)
  (s.FlightModes_LGA_Active) = (sn.FlightModes_LGA_Active)
  (s.FlightModes_Modes_On) = (sn.FlightModes_Modes_On)
  (s.FlightModes_ALTSEL_Track) = (sn.FlightModes_ALTSEL_Track)
  (s.FlightModes_VAPPR_Selected) =
  (sn.FlightModes_VAPPR_Selected)
  (s.FlightModes_ALTSEL_Active) =
  (sn.FlightModes_ALTSEL_Active)
  (s.FlightModes_PITCH_Active) = (sn.FlightModes_PITCH_Active)
  (s.FlightModes_NAV_Active) = (sn.FlightModes_NAV_Active)
  (s.FlightModes_ROLL_Active) = (sn.FlightModes_ROLL_Active)
  (s.FlightModes_ALTSEL_Selected) =
  (sn.FlightModes_ALTSEL_Selected)
  (s.FlightModes_VGA_Selected) = (sn.FlightModes_VGA_Selected)
  (s.FlightModes_VAPPR_Active) = (sn.FlightModes_VAPPR_Active)
  (s.FlightModes_LAPPR_Selected) =
  (sn.FlightModes_LAPPR_Selected)
  (s.FlightModes_VS_Active) = (sn.FlightModes_VS_Active)
  (s.FlightModes_LAPPR_Active) = (sn.FlightModes_LAPPR_Active)
  (s.FlightModes_LGA_Selected) = (sn.FlightModes_LGA_Selected)
  (s.FlightModes_FLC_Active) = (sn.FlightModes_FLC_Active)
  (s.FlightModes_FD_On) = (sn.FlightModes_FD_On)
  (s.FlightModes_ALT_Selected) = (sn.FlightModes_ALT_Selected)
  (s.FlightModes_Independent_Mode) =
  (sn.FlightModes_Independent_Mode)
  (s.FlightModes_HDG_Active) = (sn.FlightModes_HDG_Active)
  (s.FlightModes_VS_Selected) = (sn.FlightModes_VS_Selected)
  (s.FlightModes_VGA_Active) = (sn.FlightModes_VGA_Active)
  (s.FlightModes_Active_Side) = (sn.FlightModes_Active_Side)
  (s.FlightModes_NAV_Selected) = (sn.FlightModes_NAV_Selected)
  (none.(FlightModes_VERTICAL_VS.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue and
       (sn.dsh_sc_used0) = none and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none)
         else
           (((sn.dsh_events0) :> DshIntEvents) =
              ((s.dsh_events0) :> DshIntEvents))
       )
  else
    ((sn.dsh_stable).boolean/isFalse and
       (s.FlightModes_Pilot_Flying_Side) =
         (sn.FlightModes_Pilot_Flying_Side) and
       (s.FlightModes_Pilot_Flying_Transfer) =
         (sn.FlightModes_Pilot_Flying_Transfer) and
       (s.FlightModes_HDG_Switch_Pressed) =
         (sn.FlightModes_HDG_Switch_Pressed) and
       (s.FlightModes_NAV_Switch_Pressed) =
         (sn.FlightModes_NAV_Switch_Pressed) and
       (s.FlightModes_GA_Switch_Pressed) =
         (sn.FlightModes_GA_Switch_Pressed) and
       (s.FlightModes_When_AP_Engaged) =
         (sn.FlightModes_When_AP_Engaged) and
       (s.FlightModes_FD_Switch_Pressed) =
         (sn.FlightModes_FD_Switch_Pressed) and
       (s.FlightModes_Overspeed) =
         (sn.FlightModes_Overspeed) and
       (s.FlightModes_VS_Switch_Pressed) =
         (sn.FlightModes_VS_Switch_Pressed) and
       (s.FlightModes_FLC_Switch_Pressed) =
         (sn.FlightModes_FLC_Switch_Pressed) and
       (s.FlightModes_ALT_Switch_Pressed) =
         (sn.FlightModes_ALT_Switch_Pressed) and
       (s.FlightModes_APPR_Switch_Pressed) =
         (sn.FlightModes_APPR_Switch_Pressed) and
       (s.FlightModes_VS_Pitch_Wheel_Rotated) =
         (sn.FlightModes_VS_Pitch_Wheel_Rotated) and
       (s.FlightModes_Selected_NAV_Source_Changed) =
         (sn.FlightModes_Selected_NAV_Source_Changed) and
       (s.FlightModes_Selected_NAV_Frequency_Changed) =
         (sn.FlightModes_Selected_NAV_Frequency_Changed) and
       (s.FlightModes_Is_AP_Engaged) =
         (sn.FlightModes_Is_AP_Engaged) and
       (s.FlightModes_Is_Offside_FD_On) =
         (sn.FlightModes_Is_Offside_FD_On) and
       (s.FlightModes_LAPPR_Capture_Condition_Met) =
         (sn.FlightModes_LAPPR_Capture_Condition_Met) and
       (s.FlightModes_SYNC_Switch_Pressed) =
         (sn.FlightModes_SYNC_Switch_Pressed) and
       (s.FlightModes_NAV_Capture_Condition_Met) =
         (sn.FlightModes_NAV_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Target_Changed) =
         (sn.FlightModes_ALTSEL_Target_Changed) and
       (s.FlightModes_ALTSEL_Capture_Condition_Met) =
         (sn.FlightModes_ALTSEL_Capture_Condition_Met) and
       (s.FlightModes_ALTSEL_Track_Condition_Met) =
         (sn.FlightModes_ALTSEL_Track_Condition_Met) and
       (s.FlightModes_VAPPR_Capture_Condition_Met) =
         (sn.FlightModes_VAPPR_Capture_Condition_Met) and
       ((s.dsh_stable).boolean/isTrue)=>
           (((sn.dsh_events0) :> DshIntEvents) = none and
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + FlightModes_VERTICAL_VS))
       )

}

pred FlightModes_VERTICAL_VS_NewVerticalModeActivated_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  some
(FlightModes_VERTICAL_VS_SELECTED_ACTIVE & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) and
  FlightModes_VERTICAL_New_Vertical_Mode_Activated in
    ((s.dsh_events0) + dsh_genEvs0)
}

pred FlightModes_VERTICAL_VS_NewVerticalModeActivated [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.FlightModes_VERTICAL_VS_NewVerticalModeActivated_pre
  sn.(s.FlightModes_VERTICAL_VS_NewVerticalModeActivated_post)
}

pred _nextIsStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	dsh_scp0: DshStates,
	dsh_genEvs0: DshEvents] {
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_LAPPR_Capture_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_ALT_NewVerticalModeActivated_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_NAV_Select_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_NAV_NewLateralModeActivated_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_ANNUNCIATIONS_TurnAnnunciationsOn_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_VAPPR_NewVerticalModeActivated_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_ANNUNCIATIONS_TurnAnnunciationsOff_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_HDG_NewLateralModeActivated_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_LGA_Select_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_FLC_Clear_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_LGA_Clear_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_NAV_Clear_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_PITCH_Select_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_ALTSEL_Select_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_VAPPR_Capture_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_VAPPR_Select_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_ALT_Clear_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_ALTSEL_Clear_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_VGA_Clear_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_FD_TurnFDOff_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_ROLL_Clear_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_FD_TurnFDOn_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_LAPPR_Clear_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_ALTSEL_Capture_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_VAPPR_Clear_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_LGA_NewLateralModeActivated_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_HDG_Select_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_VS_Select_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_FLC_Select_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_NAV_Capture_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_ALT_Select_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_VGA_NewVerticalModeActivated_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_HDG_Clear_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_PITCH_Clear_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_VGA_Select_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_LAPPR_NewLateralModeActivated_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_LAPPR_Select_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_LATERAL_ROLL_Select_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_ALTSEL_Track_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_ALTSEL_NewVerticalModeActivated_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_VS_Clear_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_FLC_NewVerticalModeActivated_enabledAfterStep))))
  !(dsh_genEvs0.(dsh_scp0.(sn.(s.FlightModes_VERTICAL_VS_NewVerticalModeActivated_enabledAfterStep))))
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_stable) = (s.dsh_stable)
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_sc_used0) = (s.dsh_sc_used0)
  (sn.dsh_events0) = (s.dsh_events0)
  (sn.FlightModes_FD_On) = (s.FlightModes_FD_On)
  (sn.FlightModes_Modes_On) = (s.FlightModes_Modes_On)
  (sn.FlightModes_HDG_Selected) = (s.FlightModes_HDG_Selected)
  (sn.FlightModes_HDG_Active) = (s.FlightModes_HDG_Active)
  (sn.FlightModes_NAV_Selected) = (s.FlightModes_NAV_Selected)
  (sn.FlightModes_NAV_Active) = (s.FlightModes_NAV_Active)
  (sn.FlightModes_VS_Active) = (s.FlightModes_VS_Active)
  (sn.FlightModes_LAPPR_Selected) =
  (s.FlightModes_LAPPR_Selected)
  (sn.FlightModes_LAPPR_Active) = (s.FlightModes_LAPPR_Active)
  (sn.FlightModes_LGA_Selected) = (s.FlightModes_LGA_Selected)
  (sn.FlightModes_LGA_Active) = (s.FlightModes_LGA_Active)
  (sn.FlightModes_ROLL_Active) = (s.FlightModes_ROLL_Active)
  (sn.FlightModes_ROLL_Selected) =
  (s.FlightModes_ROLL_Selected)
  (sn.FlightModes_VS_Selected) = (s.FlightModes_VS_Selected)
  (sn.FlightModes_FLC_Selected) = (s.FlightModes_FLC_Selected)
  (sn.FlightModes_FLC_Active) = (s.FlightModes_FLC_Active)
  (sn.FlightModes_ALT_Active) = (s.FlightModes_ALT_Active)
  (sn.FlightModes_ALTSEL_Active) =
  (s.FlightModes_ALTSEL_Active)
  (sn.FlightModes_ALT_Selected) = (s.FlightModes_ALT_Selected)
  (sn.FlightModes_ALTSEL_Track) = (s.FlightModes_ALTSEL_Track)
  (sn.FlightModes_ALTSEL_Selected) =
  (s.FlightModes_ALTSEL_Selected)
  (sn.FlightModes_PITCH_Selected) =
  (s.FlightModes_PITCH_Selected)
  (sn.FlightModes_VAPPR_Selected) =
  (s.FlightModes_VAPPR_Selected)
  (sn.FlightModes_VAPPR_Active) = (s.FlightModes_VAPPR_Active)
  (sn.FlightModes_VGA_Selected) = (s.FlightModes_VGA_Selected)
  (sn.FlightModes_VGA_Active) = (s.FlightModes_VGA_Active)
  (sn.FlightModes_PITCH_Active) = (s.FlightModes_PITCH_Active)
  (sn.FlightModes_Independent_Mode) =
  (s.FlightModes_Independent_Mode)
  (sn.FlightModes_Active_Side) = (s.FlightModes_Active_Side)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.FlightModes_LATERAL_LAPPR_Capture) or
    sn.(s.FlightModes_VERTICAL_ALT_NewVerticalModeActivated) or
    sn.(s.FlightModes_LATERAL_NAV_Select) or
    sn.(s.FlightModes_LATERAL_NAV_NewLateralModeActivated) or
    sn.(s.FlightModes_ANNUNCIATIONS_TurnAnnunciationsOn) or
    sn.(s.FlightModes_VERTICAL_VAPPR_NewVerticalModeActivated) or
    sn.(s.FlightModes_ANNUNCIATIONS_TurnAnnunciationsOff) or
    sn.(s.FlightModes_LATERAL_HDG_NewLateralModeActivated) or
    sn.(s.FlightModes_LATERAL_LGA_Select) or
    sn.(s.FlightModes_VERTICAL_FLC_Clear) or
    sn.(s.FlightModes_LATERAL_LGA_Clear) or
    sn.(s.FlightModes_LATERAL_NAV_Clear) or
    sn.(s.FlightModes_VERTICAL_PITCH_Select) or
    sn.(s.FlightModes_VERTICAL_ALTSEL_Select) or
    sn.(s.FlightModes_VERTICAL_VAPPR_Capture) or
    sn.(s.FlightModes_VERTICAL_VAPPR_Select) or
    sn.(s.FlightModes_VERTICAL_ALT_Clear) or
    sn.(s.FlightModes_VERTICAL_ALTSEL_Clear) or
    sn.(s.FlightModes_VERTICAL_VGA_Clear) or
    sn.(s.FlightModes_FD_TurnFDOff) or
    sn.(s.FlightModes_LATERAL_ROLL_Clear) or
    sn.(s.FlightModes_FD_TurnFDOn) or
    sn.(s.FlightModes_LATERAL_LAPPR_Clear) or
    sn.(s.FlightModes_VERTICAL_ALTSEL_Capture) or
    sn.(s.FlightModes_VERTICAL_VAPPR_Clear) or
    sn.(s.FlightModes_LATERAL_LGA_NewLateralModeActivated) or
    sn.(s.FlightModes_LATERAL_HDG_Select) or
    sn.(s.FlightModes_VERTICAL_VS_Select) or
    sn.(s.FlightModes_VERTICAL_FLC_Select) or
    sn.(s.FlightModes_LATERAL_NAV_Capture) or
    sn.(s.FlightModes_VERTICAL_ALT_Select) or
    sn.(s.FlightModes_VERTICAL_VGA_NewVerticalModeActivated) or
    sn.(s.FlightModes_LATERAL_HDG_Clear) or
    sn.(s.FlightModes_VERTICAL_PITCH_Clear) or
    sn.(s.FlightModes_VERTICAL_VGA_Select) or
    sn.(s.FlightModes_LATERAL_LAPPR_NewLateralModeActivated) or
    sn.(s.FlightModes_LATERAL_LAPPR_Select) or
    sn.(s.FlightModes_LATERAL_ROLL_Select) or
    sn.(s.FlightModes_VERTICAL_ALTSEL_Track) or
    sn.(s.FlightModes_VERTICAL_ALTSEL_NewVerticalModeActivated) or
    sn.(s.FlightModes_VERTICAL_VS_Clear) or
    sn.(s.FlightModes_VERTICAL_FLC_NewVerticalModeActivated) or
    sn.(s.FlightModes_VERTICAL_VS_NewVerticalModeActivated) or
    !({ s.FlightModes_LATERAL_LAPPR_Capture_pre or
          s.FlightModes_VERTICAL_ALT_NewVerticalModeActivated_pre or
          s.FlightModes_LATERAL_NAV_Select_pre or
          s.FlightModes_LATERAL_NAV_NewLateralModeActivated_pre or
          s.FlightModes_ANNUNCIATIONS_TurnAnnunciationsOn_pre or
          s.FlightModes_VERTICAL_VAPPR_NewVerticalModeActivated_pre or
          s.FlightModes_ANNUNCIATIONS_TurnAnnunciationsOff_pre or
          s.FlightModes_LATERAL_HDG_NewLateralModeActivated_pre or
          s.FlightModes_LATERAL_LGA_Select_pre or
          s.FlightModes_VERTICAL_FLC_Clear_pre or
          s.FlightModes_LATERAL_LGA_Clear_pre or
          s.FlightModes_LATERAL_NAV_Clear_pre or
          s.FlightModes_VERTICAL_PITCH_Select_pre or
          s.FlightModes_VERTICAL_ALTSEL_Select_pre or
          s.FlightModes_VERTICAL_VAPPR_Capture_pre or
          s.FlightModes_VERTICAL_VAPPR_Select_pre or
          s.FlightModes_VERTICAL_ALT_Clear_pre or
          s.FlightModes_VERTICAL_ALTSEL_Clear_pre or
          s.FlightModes_VERTICAL_VGA_Clear_pre or
          s.FlightModes_FD_TurnFDOff_pre or
          s.FlightModes_LATERAL_ROLL_Clear_pre or
          s.FlightModes_FD_TurnFDOn_pre or
          s.FlightModes_LATERAL_LAPPR_Clear_pre or
          s.FlightModes_VERTICAL_ALTSEL_Capture_pre or
          s.FlightModes_VERTICAL_VAPPR_Clear_pre or
          s.FlightModes_LATERAL_LGA_NewLateralModeActivated_pre or
          s.FlightModes_LATERAL_HDG_Select_pre or
          s.FlightModes_VERTICAL_VS_Select_pre or
          s.FlightModes_VERTICAL_FLC_Select_pre or
          s.FlightModes_LATERAL_NAV_Capture_pre or
          s.FlightModes_VERTICAL_ALT_Select_pre or
          s.FlightModes_VERTICAL_VGA_NewVerticalModeActivated_pre or
          s.FlightModes_LATERAL_HDG_Clear_pre or
          s.FlightModes_VERTICAL_PITCH_Clear_pre or
          s.FlightModes_VERTICAL_VGA_Select_pre or
          s.FlightModes_LATERAL_LAPPR_NewLateralModeActivated_pre or
          s.FlightModes_LATERAL_LAPPR_Select_pre or
          s.FlightModes_LATERAL_ROLL_Select_pre or
          s.FlightModes_VERTICAL_ALTSEL_Track_pre or
          s.FlightModes_VERTICAL_ALTSEL_NewVerticalModeActivated_pre or
          s.FlightModes_VERTICAL_VS_Clear_pre or
          s.FlightModes_VERTICAL_FLC_NewVerticalModeActivated_pre or
          s.FlightModes_VERTICAL_VS_NewVerticalModeActivated_pre }) and
      sn.(s.dsh_stutter) }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}

