/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-07-20 14:30:02
*/

open util/boolean
open util/tcmc[DshSnapshot]

/*  BEGIN_ALDB_CONF
 *
 *  stateSigName: DshSnapshot
 *  transitionConstraintName: dsh_small_step
 *  initPredicateName: dsh_initial
 *
 *  END_ALDB_CONF
 */

/* The DigitalWatch case study - Dash model

Copyright (c) 2018 Jose Serna <jserna@uwaterloo.ca>
Copyright (c) 2018,2022 Nancy Day <nday@uwaterloo.ca>

This file is part of the DigitalWatch Dash model.

The DigitalWatch Dash model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The DigitalWatch Dash model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the DigitalWatch Dash model.  If not, see
<https://www.gnu.org/licenses/>.


The DigitalWatch case study is described
in~\cite{DBLP:journals/scp/Harel87} by Harel.  The DigitalWatch Dash
model is an adaptation of the original model(s) presented there.

@Article{DBLP:journals/scp/Harel87,
  author    = {David Harel},
  title     = {Statecharts: {A} Visual Formalism for Complex Systems},
  year      = 1987,
  volume    = 8,
  number    = 3,
  pages     = {231-274},
  doi       = {10.1016/0167-6423(87)90035-9},
  url       = {https://doi.org/10.1016/0167-6423(87)90035-9},
  journal   = {Sci. Comput. Program.},
  timestamp = {Wed, 14 Nov 2018 10:21:28 +0100},
  biburl    = {https://dblp.org/rec/bib/journals/scp/Harel87},
  bibsource = {dblp computer science bibliography, https://dblp.org}
}

This model has appeared in the following publications:

@inproceedings{DBLP:conf/re/AbbassiBDS18,
  author    = {Ali Abbassi and
               Amin Bandali and
               Nancy A. Day and
               Jos{\'{e}} Serna},
  editor    = {Ana Moreira and
               Gunter Mussbacher and
               Jo{\~{a}}o Ara{\'{u}}jo and
               Pablo S{\'{a}}nchez},
  title     = {A Comparison of the Declarative Modelling Languages B, Dash, and {TLA+}},
  booktitle = {8th {IEEE} International Model-Driven Requirements Engineering Workshop,
               MoDRE@RE 2018, Banff, AB, Canada, August 20, 2018},
  pages     = {11--20},
  publisher = {{IEEE} Computer Society},
  year      = {2018},
  url       = {https://doi.org/10.1109/MoDRE.2018.00008},
  doi       = {10.1109/MoDRE.2018.00008},
  timestamp = {Wed, 16 Oct 2019 14:14:56 +0200},
  biburl    = {https://dblp.org/rec/conf/re/AbbassiBDS18.bib},
  bibsource = {dblp computer science bibliography, https://dblp.org}
}

@mastersthesis{bandali2020,
  type      = {{MMath} thesis},
  author    = {Amin Bandali},
  title     = {{A Comprehensive Study of Declarative Modelling Languages}},
  school    = "University of Waterloo, David R. Cheriton School of Computer Science",
  year      = 2020,
  month     = {July},
  publisher = "UWSpace",
  url       = {http://hdl.handle.net/10012/16059},
  note      = {\url{http://hdl.handle.net/10012/16059} and
                  \url{https://bndl.org/mmath}},
  pdf       = {https://p.bndl.org/bandali-mmath-thesis.pdf}
}

*/

abstract sig DshStates {}
abstract sig DigitalWatch extends DshStates {} 
abstract sig DshScopes {}
one sig DigitalWatchScope extends DshScopes {} 
one sig DigitalWatch_LightScope extends DshScopes {} 
abstract sig DigitalWatch_Light extends DigitalWatch {} 
one sig DigitalWatch_Light_Off extends DigitalWatch_Light {} 
one sig DigitalWatch_Light_On extends DigitalWatch_Light {} 
one sig DigitalWatch_MainScope extends DshScopes {} 
abstract sig DigitalWatch_Main extends DigitalWatch {} 
abstract sig DigitalWatch_Main_Displays extends DigitalWatch_Main {} 
one sig DigitalWatch_Main_Displays_Time extends DigitalWatch_Main_Displays {} 
one sig DigitalWatch_Main_Displays_Date extends DigitalWatch_Main_Displays {} 
one sig DigitalWatch_Main_Displays_Wait extends DigitalWatch_Main_Displays {} 
one sig DigitalWatch_Main_Displays_Update extends DigitalWatch_Main_Displays {} 
one sig DigitalWatch_Main_Displays_Alarm1 extends DigitalWatch_Main_Displays {} 
one sig DigitalWatch_Main_Displays_Alarm2 extends DigitalWatch_Main_Displays {} 
one sig DigitalWatch_Main_Displays_Chime extends DigitalWatch_Main_Displays {} 
one sig DigitalWatch_Main_Displays_StopWatch extends DigitalWatch_Main_Displays {} 

abstract sig Transitions {}
one sig NO_TRANS extends Transitions {} 
one sig DigitalWatch_Main_Displays_Date_return_to_time extends Transitions {} 
one sig DigitalWatch_Main_Displays_Date_show_time extends Transitions {} 
one sig DigitalWatch_Main_Displays_Update_show_time extends Transitions {} 
one sig DigitalWatch_Main_Displays_Alarm2_go2chime extends Transitions {} 
one sig DigitalWatch_Main_Displays_Time_try_update extends Transitions {} 
one sig DigitalWatch_Main_Displays_Wait_show_update extends Transitions {} 
one sig DigitalWatch_Light_Off_light_on extends Transitions {} 
one sig DigitalWatch_Light_On_light_off extends Transitions {} 
one sig DigitalWatch_Main_Displays_Chime_go2Stopwatch extends Transitions {} 
one sig DigitalWatch_Main_Displays_Time_go2alarm1 extends Transitions {} 
one sig DigitalWatch_Main_Displays_Time_show_date extends Transitions {} 
one sig DigitalWatch_Main_Displays_Wait_show_time extends Transitions {} 
one sig DigitalWatch_Main_Displays_Alarm1_go2alarm2 extends Transitions {} 
one sig DigitalWatch_Main_Displays_StopWatch_go2Time extends Transitions {} 

abstract sig DshEvents {}
abstract sig DshIntEvents extends DshEvents {} 
one sig DigitalWatch_Main_Displays_Date_waited_2_min extends DshIntEvents {} 
one sig DigitalWatch_Main_Displays_Wait_waited_2_sec extends DshIntEvents {} 
abstract sig DshEnvEvents extends DshEvents {} 
one sig DigitalWatch_press_a extends DshEnvEvents {} 
one sig DigitalWatch_release_a extends DshEnvEvents {} 
one sig DigitalWatch_press_b extends DshEnvEvents {} 
one sig DigitalWatch_release_b extends DshEnvEvents {} 
one sig DigitalWatch_press_c extends DshEnvEvents {} 
one sig DigitalWatch_release_c extends DshEnvEvents {} 
one sig DigitalWatch_press_d extends DshEnvEvents {} 
one sig DigitalWatch_release_d extends DshEnvEvents {} 

sig DshSnapshot {
  dsh_sc_used0: set DshScopes,
  dsh_conf0: set DshStates,
  dsh_taken0: set Transitions,
  dsh_events0: set DshEvents,
  dsh_stable: one boolean/Bool
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) =
  (DigitalWatch_Light_Off + DigitalWatch_Main_Displays_Time) &&
  (s.dsh_sc_used0) = none &&
  (s.dsh_taken0) = NO_TRANS &&
  ((s.dsh_events0) :> DshIntEvents) = none
  (s.dsh_stable).boolean/isTrue
}

pred DigitalWatch_Main_Displays_Date_return_to_time_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Main_Displays_Date & (s.dsh_conf0))
  !(DigitalWatch_MainScope in (s.dsh_sc_used0))
  !((s.dsh_stable).boolean/isTrue) &&
  DigitalWatch_Main_Displays_Date_waited_2_min in
    (s.dsh_events0)
}


pred DigitalWatch_Main_Displays_Date_return_to_time_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((((((DigitalWatch_Main_Displays_Time +
               DigitalWatch_Main_Displays_Date) +
              DigitalWatch_Main_Displays_Wait) +
             DigitalWatch_Main_Displays_Update) +
            DigitalWatch_Main_Displays_Alarm1) +
           DigitalWatch_Main_Displays_Alarm2) +
          DigitalWatch_Main_Displays_Chime) +
         DigitalWatch_Main_Displays_StopWatch)) +
     DigitalWatch_Main_Displays_Time)
  (sn.dsh_taken0) =
  DigitalWatch_Main_Displays_Date_return_to_time
  {(none.(DigitalWatch_Main.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_MainScope))}
       )}

}

pred DigitalWatch_Main_Displays_Date_return_to_time_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Main_Displays_Date & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) &&
  DigitalWatch_Main_Displays_Date_waited_2_min in
    ((s.dsh_events0) + genEvs0)
}

pred DigitalWatch_Main_Displays_Date_return_to_time [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Main_Displays_Date_return_to_time_pre
  sn.(s.DigitalWatch_Main_Displays_Date_return_to_time_post)
}

pred DigitalWatch_Main_Displays_Date_show_time_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Main_Displays_Date & (s.dsh_conf0))
  !(DigitalWatch_MainScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (DigitalWatch_press_d in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (DigitalWatch_press_d in (s.dsh_events0))}

}


pred DigitalWatch_Main_Displays_Date_show_time_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((((((DigitalWatch_Main_Displays_Time +
               DigitalWatch_Main_Displays_Date) +
              DigitalWatch_Main_Displays_Wait) +
             DigitalWatch_Main_Displays_Update) +
            DigitalWatch_Main_Displays_Alarm1) +
           DigitalWatch_Main_Displays_Alarm2) +
          DigitalWatch_Main_Displays_Chime) +
         DigitalWatch_Main_Displays_StopWatch)) +
     DigitalWatch_Main_Displays_Time)
  (sn.dsh_taken0) = DigitalWatch_Main_Displays_Date_show_time
  {(none.(DigitalWatch_Main.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_MainScope))}
       )}

}

pred DigitalWatch_Main_Displays_Date_show_time_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Main_Displays_Date & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(DigitalWatch_Main in sc0) &&
       DigitalWatch_press_d in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (DigitalWatch_press_d in ((s.dsh_events0) + genEvs0))}

}

pred DigitalWatch_Main_Displays_Date_show_time [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Main_Displays_Date_show_time_pre
  sn.(s.DigitalWatch_Main_Displays_Date_show_time_post)
}

pred DigitalWatch_Main_Displays_Update_show_time_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Main_Displays_Update & (s.dsh_conf0))
  !(DigitalWatch_MainScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (DigitalWatch_press_b in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (DigitalWatch_press_b in (s.dsh_events0))}

}


pred DigitalWatch_Main_Displays_Update_show_time_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((((((DigitalWatch_Main_Displays_Time +
               DigitalWatch_Main_Displays_Date) +
              DigitalWatch_Main_Displays_Wait) +
             DigitalWatch_Main_Displays_Update) +
            DigitalWatch_Main_Displays_Alarm1) +
           DigitalWatch_Main_Displays_Alarm2) +
          DigitalWatch_Main_Displays_Chime) +
         DigitalWatch_Main_Displays_StopWatch)) +
     DigitalWatch_Main_Displays_Time)
  (sn.dsh_taken0) =
  DigitalWatch_Main_Displays_Update_show_time
  {(none.(DigitalWatch_Main.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_MainScope))}
       )}

}

pred DigitalWatch_Main_Displays_Update_show_time_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Main_Displays_Update & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(DigitalWatch_Main in sc0) &&
       DigitalWatch_press_b in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (DigitalWatch_press_b in ((s.dsh_events0) + genEvs0))}

}

pred DigitalWatch_Main_Displays_Update_show_time [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Main_Displays_Update_show_time_pre
  sn.(s.DigitalWatch_Main_Displays_Update_show_time_post)
}

pred DigitalWatch_Main_Displays_Alarm2_go2chime_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Main_Displays_Alarm2 & (s.dsh_conf0))
  !(DigitalWatch_MainScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (DigitalWatch_press_a in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (DigitalWatch_press_a in (s.dsh_events0))}

}


pred DigitalWatch_Main_Displays_Alarm2_go2chime_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((((((DigitalWatch_Main_Displays_Time +
               DigitalWatch_Main_Displays_Date) +
              DigitalWatch_Main_Displays_Wait) +
             DigitalWatch_Main_Displays_Update) +
            DigitalWatch_Main_Displays_Alarm1) +
           DigitalWatch_Main_Displays_Alarm2) +
          DigitalWatch_Main_Displays_Chime) +
         DigitalWatch_Main_Displays_StopWatch)) +
     DigitalWatch_Main_Displays_Chime)
  (sn.dsh_taken0) = DigitalWatch_Main_Displays_Alarm2_go2chime
  {(none.(DigitalWatch_Main.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_MainScope))}
       )}

}

pred DigitalWatch_Main_Displays_Alarm2_go2chime_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Main_Displays_Alarm2 & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(DigitalWatch_Main in sc0) &&
       DigitalWatch_press_a in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (DigitalWatch_press_a in ((s.dsh_events0) + genEvs0))}

}

pred DigitalWatch_Main_Displays_Alarm2_go2chime [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Main_Displays_Alarm2_go2chime_pre
  sn.(s.DigitalWatch_Main_Displays_Alarm2_go2chime_post)
}

pred DigitalWatch_Main_Displays_Time_try_update_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Main_Displays_Time & (s.dsh_conf0))
  !(DigitalWatch_MainScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (DigitalWatch_press_c in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (DigitalWatch_press_c in (s.dsh_events0))}

}


pred DigitalWatch_Main_Displays_Time_try_update_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((((((DigitalWatch_Main_Displays_Time +
               DigitalWatch_Main_Displays_Date) +
              DigitalWatch_Main_Displays_Wait) +
             DigitalWatch_Main_Displays_Update) +
            DigitalWatch_Main_Displays_Alarm1) +
           DigitalWatch_Main_Displays_Alarm2) +
          DigitalWatch_Main_Displays_Chime) +
         DigitalWatch_Main_Displays_StopWatch)) +
     DigitalWatch_Main_Displays_Wait)
  (sn.dsh_taken0) = DigitalWatch_Main_Displays_Time_try_update
  {(none.(DigitalWatch_Main.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_MainScope))}
       )}

}

pred DigitalWatch_Main_Displays_Time_try_update_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Main_Displays_Time & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(DigitalWatch_Main in sc0) &&
       DigitalWatch_press_c in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (DigitalWatch_press_c in ((s.dsh_events0) + genEvs0))}

}

pred DigitalWatch_Main_Displays_Time_try_update [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Main_Displays_Time_try_update_pre
  sn.(s.DigitalWatch_Main_Displays_Time_try_update_post)
}

pred DigitalWatch_Main_Displays_Wait_show_update_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Main_Displays_Wait & (s.dsh_conf0))
  !(DigitalWatch_MainScope in (s.dsh_sc_used0))
  !((s.dsh_stable).boolean/isTrue) &&
  DigitalWatch_Main_Displays_Wait_waited_2_sec in
    (s.dsh_events0)
}


pred DigitalWatch_Main_Displays_Wait_show_update_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((((((DigitalWatch_Main_Displays_Time +
               DigitalWatch_Main_Displays_Date) +
              DigitalWatch_Main_Displays_Wait) +
             DigitalWatch_Main_Displays_Update) +
            DigitalWatch_Main_Displays_Alarm1) +
           DigitalWatch_Main_Displays_Alarm2) +
          DigitalWatch_Main_Displays_Chime) +
         DigitalWatch_Main_Displays_StopWatch)) +
     DigitalWatch_Main_Displays_Update)
  (sn.dsh_taken0) =
  DigitalWatch_Main_Displays_Wait_show_update
  {(none.(DigitalWatch_Main.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_MainScope))}
       )}

}

pred DigitalWatch_Main_Displays_Wait_show_update_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Main_Displays_Wait & (sn.dsh_conf0))
  !((s.dsh_stable).boolean/isTrue) &&
  DigitalWatch_Main_Displays_Wait_waited_2_sec in
    ((s.dsh_events0) + genEvs0)
}

pred DigitalWatch_Main_Displays_Wait_show_update [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Main_Displays_Wait_show_update_pre
  sn.(s.DigitalWatch_Main_Displays_Wait_show_update_post)
}

pred DigitalWatch_Light_Off_light_on_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Light_Off & (s.dsh_conf0))
  !(DigitalWatch_LightScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (DigitalWatch_press_b in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (DigitalWatch_press_b in (s.dsh_events0))}

}


pred DigitalWatch_Light_Off_light_on_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (DigitalWatch_Light_Off + DigitalWatch_Light_On)) +
     DigitalWatch_Light_On)
  (sn.dsh_taken0) = DigitalWatch_Light_Off_light_on
  {(none.(DigitalWatch_Light.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_LightScope))}
       )}

}

pred DigitalWatch_Light_Off_light_on_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Light_Off & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(DigitalWatch_Light in sc0) &&
       DigitalWatch_press_b in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (DigitalWatch_press_b in ((s.dsh_events0) + genEvs0))}

}

pred DigitalWatch_Light_Off_light_on [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Light_Off_light_on_pre
  sn.(s.DigitalWatch_Light_Off_light_on_post)
}

pred DigitalWatch_Light_On_light_off_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Light_On & (s.dsh_conf0))
  !(DigitalWatch_LightScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (DigitalWatch_release_b in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (DigitalWatch_release_b in (s.dsh_events0))}

}


pred DigitalWatch_Light_On_light_off_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (DigitalWatch_Light_Off + DigitalWatch_Light_On)) +
     DigitalWatch_Light_Off)
  (sn.dsh_taken0) = DigitalWatch_Light_On_light_off
  {(none.(DigitalWatch_Light.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_LightScope))}
       )}

}

pred DigitalWatch_Light_On_light_off_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Light_On & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(DigitalWatch_Light in sc0) &&
       DigitalWatch_release_b in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (DigitalWatch_release_b in ((s.dsh_events0) + genEvs0))}

}

pred DigitalWatch_Light_On_light_off [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Light_On_light_off_pre
  sn.(s.DigitalWatch_Light_On_light_off_post)
}

pred DigitalWatch_Main_Displays_Chime_go2Stopwatch_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Main_Displays_Chime & (s.dsh_conf0))
  !(DigitalWatch_MainScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (DigitalWatch_press_a in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (DigitalWatch_press_a in (s.dsh_events0))}

}


pred DigitalWatch_Main_Displays_Chime_go2Stopwatch_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((((((DigitalWatch_Main_Displays_Time +
               DigitalWatch_Main_Displays_Date) +
              DigitalWatch_Main_Displays_Wait) +
             DigitalWatch_Main_Displays_Update) +
            DigitalWatch_Main_Displays_Alarm1) +
           DigitalWatch_Main_Displays_Alarm2) +
          DigitalWatch_Main_Displays_Chime) +
         DigitalWatch_Main_Displays_StopWatch)) +
     DigitalWatch_Main_Displays_StopWatch)
  (sn.dsh_taken0) =
  DigitalWatch_Main_Displays_Chime_go2Stopwatch
  {(none.(DigitalWatch_Main.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_MainScope))}
       )}

}

pred DigitalWatch_Main_Displays_Chime_go2Stopwatch_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Main_Displays_Chime & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(DigitalWatch_Main in sc0) &&
       DigitalWatch_press_a in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (DigitalWatch_press_a in ((s.dsh_events0) + genEvs0))}

}

pred DigitalWatch_Main_Displays_Chime_go2Stopwatch [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Main_Displays_Chime_go2Stopwatch_pre
  sn.(s.DigitalWatch_Main_Displays_Chime_go2Stopwatch_post)
}

pred DigitalWatch_Main_Displays_Time_go2alarm1_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Main_Displays_Time & (s.dsh_conf0))
  !(DigitalWatch_MainScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (DigitalWatch_press_a in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (DigitalWatch_press_a in (s.dsh_events0))}

}


pred DigitalWatch_Main_Displays_Time_go2alarm1_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((((((DigitalWatch_Main_Displays_Time +
               DigitalWatch_Main_Displays_Date) +
              DigitalWatch_Main_Displays_Wait) +
             DigitalWatch_Main_Displays_Update) +
            DigitalWatch_Main_Displays_Alarm1) +
           DigitalWatch_Main_Displays_Alarm2) +
          DigitalWatch_Main_Displays_Chime) +
         DigitalWatch_Main_Displays_StopWatch)) +
     DigitalWatch_Main_Displays_Alarm1)
  (sn.dsh_taken0) = DigitalWatch_Main_Displays_Time_go2alarm1
  {(none.(DigitalWatch_Main.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_MainScope))}
       )}

}

pred DigitalWatch_Main_Displays_Time_go2alarm1_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Main_Displays_Time & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(DigitalWatch_Main in sc0) &&
       DigitalWatch_press_a in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (DigitalWatch_press_a in ((s.dsh_events0) + genEvs0))}

}

pred DigitalWatch_Main_Displays_Time_go2alarm1 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Main_Displays_Time_go2alarm1_pre
  sn.(s.DigitalWatch_Main_Displays_Time_go2alarm1_post)
}

pred DigitalWatch_Main_Displays_Time_show_date_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Main_Displays_Time & (s.dsh_conf0))
  !(DigitalWatch_MainScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (DigitalWatch_press_d in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (DigitalWatch_press_d in (s.dsh_events0))}

}


pred DigitalWatch_Main_Displays_Time_show_date_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((((((DigitalWatch_Main_Displays_Time +
               DigitalWatch_Main_Displays_Date) +
              DigitalWatch_Main_Displays_Wait) +
             DigitalWatch_Main_Displays_Update) +
            DigitalWatch_Main_Displays_Alarm1) +
           DigitalWatch_Main_Displays_Alarm2) +
          DigitalWatch_Main_Displays_Chime) +
         DigitalWatch_Main_Displays_StopWatch)) +
     DigitalWatch_Main_Displays_Date)
  (sn.dsh_taken0) = DigitalWatch_Main_Displays_Time_show_date
  {(none.(DigitalWatch_Main.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_MainScope))}
       )}

}

pred DigitalWatch_Main_Displays_Time_show_date_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Main_Displays_Time & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(DigitalWatch_Main in sc0) &&
       DigitalWatch_press_d in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (DigitalWatch_press_d in ((s.dsh_events0) + genEvs0))}

}

pred DigitalWatch_Main_Displays_Time_show_date [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Main_Displays_Time_show_date_pre
  sn.(s.DigitalWatch_Main_Displays_Time_show_date_post)
}

pred DigitalWatch_Main_Displays_Wait_show_time_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Main_Displays_Wait & (s.dsh_conf0))
  !(DigitalWatch_MainScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (DigitalWatch_release_c in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (DigitalWatch_release_c in (s.dsh_events0))}

}


pred DigitalWatch_Main_Displays_Wait_show_time_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((((((DigitalWatch_Main_Displays_Time +
               DigitalWatch_Main_Displays_Date) +
              DigitalWatch_Main_Displays_Wait) +
             DigitalWatch_Main_Displays_Update) +
            DigitalWatch_Main_Displays_Alarm1) +
           DigitalWatch_Main_Displays_Alarm2) +
          DigitalWatch_Main_Displays_Chime) +
         DigitalWatch_Main_Displays_StopWatch)) +
     DigitalWatch_Main_Displays_Time)
  (sn.dsh_taken0) = DigitalWatch_Main_Displays_Wait_show_time
  {(none.(DigitalWatch_Main.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_MainScope))}
       )}

}

pred DigitalWatch_Main_Displays_Wait_show_time_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Main_Displays_Wait & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(DigitalWatch_Main in sc0) &&
       DigitalWatch_release_c in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (DigitalWatch_release_c in ((s.dsh_events0) + genEvs0))}

}

pred DigitalWatch_Main_Displays_Wait_show_time [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Main_Displays_Wait_show_time_pre
  sn.(s.DigitalWatch_Main_Displays_Wait_show_time_post)
}

pred DigitalWatch_Main_Displays_Alarm1_go2alarm2_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Main_Displays_Alarm1 & (s.dsh_conf0))
  !(DigitalWatch_MainScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (DigitalWatch_press_a in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (DigitalWatch_press_a in (s.dsh_events0))}

}


pred DigitalWatch_Main_Displays_Alarm1_go2alarm2_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((((((DigitalWatch_Main_Displays_Time +
               DigitalWatch_Main_Displays_Date) +
              DigitalWatch_Main_Displays_Wait) +
             DigitalWatch_Main_Displays_Update) +
            DigitalWatch_Main_Displays_Alarm1) +
           DigitalWatch_Main_Displays_Alarm2) +
          DigitalWatch_Main_Displays_Chime) +
         DigitalWatch_Main_Displays_StopWatch)) +
     DigitalWatch_Main_Displays_Alarm2)
  (sn.dsh_taken0) =
  DigitalWatch_Main_Displays_Alarm1_go2alarm2
  {(none.(DigitalWatch_Main.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_MainScope))}
       )}

}

pred DigitalWatch_Main_Displays_Alarm1_go2alarm2_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Main_Displays_Alarm1 & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(DigitalWatch_Main in sc0) &&
       DigitalWatch_press_a in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (DigitalWatch_press_a in ((s.dsh_events0) + genEvs0))}

}

pred DigitalWatch_Main_Displays_Alarm1_go2alarm2 [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Main_Displays_Alarm1_go2alarm2_pre
  sn.(s.DigitalWatch_Main_Displays_Alarm1_go2alarm2_post)
}

pred DigitalWatch_Main_Displays_StopWatch_go2Time_pre [
	s: one DshSnapshot] {
  some (DigitalWatch_Main_Displays_StopWatch & (s.dsh_conf0))
  !(DigitalWatch_MainScope in (s.dsh_sc_used0))
  {((s.dsh_stable).boolean/isTrue)=>
    (DigitalWatch_press_a in
       ((s.dsh_events0) :> DshEnvEvents))
  else
    (DigitalWatch_press_a in (s.dsh_events0))}

}


pred DigitalWatch_Main_Displays_StopWatch_go2Time_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) =
  (((s.dsh_conf0) -
      (((((((DigitalWatch_Main_Displays_Time +
               DigitalWatch_Main_Displays_Date) +
              DigitalWatch_Main_Displays_Wait) +
             DigitalWatch_Main_Displays_Update) +
            DigitalWatch_Main_Displays_Alarm1) +
           DigitalWatch_Main_Displays_Alarm2) +
          DigitalWatch_Main_Displays_Chime) +
         DigitalWatch_Main_Displays_StopWatch)) +
     DigitalWatch_Main_Displays_Time)
  (sn.dsh_taken0) =
  DigitalWatch_Main_Displays_StopWatch_go2Time
  {(none.(DigitalWatch_Main.(sn.(s._nextIsStable))))=>
    ((sn.dsh_stable).boolean/isTrue &&
       (sn.dsh_sc_used0) = none &&
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
              (sn.dsh_sc_used0) = none)
         else
           ((sn.dsh_sc_used0) =
              ((s.dsh_sc_used0) + DigitalWatch_MainScope))}
       )}

}

pred DigitalWatch_Main_Displays_StopWatch_go2Time_enabledAfterStep [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  some (DigitalWatch_Main_Displays_StopWatch & (sn.dsh_conf0))
  {((s.dsh_stable).boolean/isTrue)=>
    (!(DigitalWatch_Main in sc0) &&
       DigitalWatch_press_a in
         (((s.dsh_events0) :> DshEnvEvents) + genEvs0))
  else
    (DigitalWatch_press_a in ((s.dsh_events0) + genEvs0))}

}

pred DigitalWatch_Main_Displays_StopWatch_go2Time [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.DigitalWatch_Main_Displays_StopWatch_go2Time_pre
  sn.(s.DigitalWatch_Main_Displays_StopWatch_go2Time_post)
}

pred _nextIsStable [
	s: one DshSnapshot,
	sn: one DshSnapshot,
	sc0: DshStates,
	genEvs0: DshEvents] {
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Main_Displays_Date_return_to_time_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Main_Displays_Date_show_time_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Main_Displays_Update_show_time_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Main_Displays_Alarm2_go2chime_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Main_Displays_Time_try_update_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Main_Displays_Wait_show_update_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Light_Off_light_on_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Light_On_light_off_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Main_Displays_Chime_go2Stopwatch_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Main_Displays_Time_go2alarm1_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Main_Displays_Time_show_date_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Main_Displays_Wait_show_time_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Main_Displays_Alarm1_go2alarm2_enabledAfterStep))))
  !(genEvs0.(sc0.(sn.(s.DigitalWatch_Main_Displays_StopWatch_go2Time_enabledAfterStep))))
}

pred dsh_stutter [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_stable) = (s.dsh_stable)
  (sn.dsh_conf0) = (s.dsh_conf0)
  (sn.dsh_sc_used0) = (s.dsh_sc_used0)
  (sn.dsh_taken0) = NO_TRANS
  ((sn.dsh_events0) :> DshIntEvents) = none
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.DigitalWatch_Main_Displays_Date_return_to_time) ||
    sn.(s.DigitalWatch_Main_Displays_Date_show_time) ||
    sn.(s.DigitalWatch_Main_Displays_Update_show_time) ||
    sn.(s.DigitalWatch_Main_Displays_Alarm2_go2chime) ||
    sn.(s.DigitalWatch_Main_Displays_Time_try_update) ||
    sn.(s.DigitalWatch_Main_Displays_Wait_show_update) ||
    sn.(s.DigitalWatch_Light_Off_light_on) ||
    sn.(s.DigitalWatch_Light_On_light_off) ||
    sn.(s.DigitalWatch_Main_Displays_Chime_go2Stopwatch) ||
    sn.(s.DigitalWatch_Main_Displays_Time_go2alarm1) ||
    sn.(s.DigitalWatch_Main_Displays_Time_show_date) ||
    sn.(s.DigitalWatch_Main_Displays_Wait_show_time) ||
    sn.(s.DigitalWatch_Main_Displays_Alarm1_go2alarm2) ||
    sn.(s.DigitalWatch_Main_Displays_StopWatch_go2Time) ||
    !({ s.DigitalWatch_Main_Displays_Date_return_to_time_pre ||
          s.DigitalWatch_Main_Displays_Date_show_time_pre ||
          s.DigitalWatch_Main_Displays_Update_show_time_pre ||
          s.DigitalWatch_Main_Displays_Alarm2_go2chime_pre ||
          s.DigitalWatch_Main_Displays_Time_try_update_pre ||
          s.DigitalWatch_Main_Displays_Wait_show_update_pre ||
          s.DigitalWatch_Light_Off_light_on_pre ||
          s.DigitalWatch_Light_On_light_off_pre ||
          s.DigitalWatch_Main_Displays_Chime_go2Stopwatch_pre ||
          s.DigitalWatch_Main_Displays_Time_go2alarm1_pre ||
          s.DigitalWatch_Main_Displays_Time_show_date_pre ||
          s.DigitalWatch_Main_Displays_Wait_show_time_pre ||
          s.DigitalWatch_Main_Displays_Alarm1_go2alarm2_pre ||
          s.DigitalWatch_Main_Displays_StopWatch_go2Time_pre }) &&
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
                   (s.dsh_stable) = (sn.dsh_stable)) =>
                  (s = sn))
}

pred dsh_enough_operations {
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Main_Displays_Date_return_to_time))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Main_Displays_Date_show_time))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Main_Displays_Update_show_time))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Main_Displays_Alarm2_go2chime))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Main_Displays_Time_try_update))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Main_Displays_Wait_show_update))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Light_Off_light_on))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Light_On_light_off))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Main_Displays_Chime_go2Stopwatch))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Main_Displays_Time_go2alarm1))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Main_Displays_Time_show_date))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Main_Displays_Wait_show_time))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Main_Displays_Alarm1_go2alarm2))
  (some s: one
  DshSnapshot,sn: one
  DshSnapshot | sn.(s.DigitalWatch_Main_Displays_StopWatch_go2Time))
}

fact dsh_single_event {
  (all s: one
  DshSnapshot | lone
  ((s.dsh_events0) :> DshEnvEvents))
}

pred dsh_reachability {
  (all s: one
  DshSnapshot | s in
                  (DshSnapshot.(tcmc/ks_s0 <: (*
                                  tcmc/ks_sigma))))
}

fact dsh_tcmc_fact {
  (all s: one
  DshSnapshot | (s in tcmc/ks_s0) <=> (s.dsh_initial))
  (all s: one
  DshSnapshot,sn: one
  DshSnapshot | ((s -> sn) in tcmc/ks_sigma) <=>
                  (sn.(s.dsh_small_step)))
}

// significant scope: at least one copy of every transition
// has to be at least 14 since there are 14 different transitions
/*
run {
    dsh_reachability 
    dsh_enough_operations 
}
for exactly 14 DshSnapshot expect 1
*/

fun is_a_next_state: set DshSnapshot {
    ex[ {s: DshSnapshot | boolean/isTrue[boolean/True] } ]
}

// this won't hold unless we force there to be a next snapshot from the one in which press_a is pressed
// note that not all states may be reachable in c/e

//NAD: before this property did not have StopWatch in antecedent
pred eventually_time {
    ctl_mc[
        ag[
            imp_ctl[and_ctl[
                    { s : DshSnapshot | DigitalWatch_press_a in s.dsh_events0
                                        && 
                                        DigitalWatch_Main_Displays_StopWatch in s.dsh_conf0},
                    is_a_next_state],
                ex[{s: DshSnapshot | DigitalWatch_Main_Displays_Time in s.dsh_conf0 }]
            ]
        ]
    ]
}

// we expect this to hold (be UNSAT)
check { eventually_time } for exactly 7 DshSnapshot expect 0

/*
    How to run this model:

    dashcli -t -m tcmc -single digital-watch.dsh
    dashcli digital-watch.als
*/
