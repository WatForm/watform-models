--------------------------- MODULE digital_watch ---------------------------
(* The DigitalWatch case study - TLA+ model

Copyright (c) 2018 Ali Abbassi <aabbassi@uwaterloo.ca>
Copyright (c) 2018 Nancy Day <nday@uwaterloo.ca>
Copyright (c) 2018-2020 Amin Bandali <bandali@uwaterloo.ca>

This file is part of the DigitalWatch TLA+ model.

The DigitalWatch TLA+ model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The DigitalWatch TLA+ model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the DigitalWatch TLA+ model.  If not, see
<https://www.gnu.org/licenses/>.


The DigitalWatch case study is described
in~\cite{DBLP:journals/scp/Harel87} by Harel.  The DigitalWatch TLA+
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

*)

EXTENDS Integers, TLC, FiniteSets, Sequences

VARIABLES
    light, status,
    waited_2_min, waited_2_sec,
    pressed

STATUS == { "Time", "Date", "Wait", "Update"
          , "Alarm1", "Alarm2", "Chime", "StopWatch"
          , "Alarms_Beep" (* doesn't seem to be used right now *)  }

KEYS == { "a", "b", "c", "d" }

vars == << light, status, waited_2_min, waited_2_sec, pressed >>

vars_but_light == << status, waited_2_min, waited_2_sec, pressed >>

vars_but_status == << light, waited_2_min, waited_2_sec, pressed >>


\* Helper predicate for range of a function
Range(f) == {f[x]: x \in DOMAIN f}


TypeOK ==  \* Typing invariant
    /\ light \in BOOLEAN  \* FALSE: Off, TRUE: On
    /\ status \in STATUS
    /\ waited_2_min \in BOOLEAN /\ waited_2_sec \in BOOLEAN
    /\ pressed \in [KEYS -> BOOLEAN]

Init ==  \* Initial state
    /\ light = FALSE  \* initially light is off
    /\ status = "Time"  \* initially display shows time
    /\ waited_2_min = FALSE /\ waited_2_sec = FALSE
    /\ pressed = [k \in KEYS |-> FALSE]


\* <Light>
light_off_light_on ==
    /\ pressed["b"]
    /\ light' = TRUE
    /\ UNCHANGED vars_but_light

light_on_light_off ==
    /\ ~pressed["b"]
    /\ light' = FALSE
    /\ UNCHANGED vars_but_light
\* </Light>


\* <Time>
time_show_date ==
    /\ status = "Time"
    /\ pressed["d"]
    /\ status' = "Date"
    /\ UNCHANGED vars_but_status

time_try_update ==
    /\ status = "Time"
    /\ pressed["c"]
    /\ status' = "Wait"
    /\ UNCHANGED vars_but_status

time_go2alarm1 ==
    /\ status = "Time"
    /\ pressed["a"]
    /\ status' = "Alarm1"
    /\ UNCHANGED vars_but_status
\* </Time>


\* <Date>
date_show_time ==
    /\ status = "Date"
    /\ pressed["d"]
    /\ status' = "Time"
    /\ UNCHANGED vars_but_status

date_return_to_time ==
    /\ status = "Date" 
    /\ waited_2_min
    /\ status' = "Time"
    /\ UNCHANGED vars_but_status
\* </Date>


\* <Wait>
wait_show_time ==
    /\ status = "Wait"
    /\ ~pressed["c"]
    /\ status' = "Time"
    /\ UNCHANGED vars_but_status

wait_show_update == 
    /\ status = "Wait"
    /\ waited_2_sec
    /\ status' = "Update"
    /\ UNCHANGED vars_but_status
\* </Wait>


\* <Update>
update_show_time ==
    /\ status = "Update"
    /\ pressed["b"]
    /\ status' = "Time"
    /\ UNCHANGED vars_but_status
\* </Update>


\* <Alarm1>
alarm1_go2alarm2 ==
    /\ status = "Alarm1"
    /\ pressed["a"]
    /\ status' = "Alarm2"
    /\ UNCHANGED vars_but_status
\* </Alarm1>


\* <Alarm2>
alarm2_go2chime ==
    /\ status = "Alarm2"
    /\ pressed["a"]
    /\ status' = "Chime"
    /\ UNCHANGED vars_but_status
\* </Alarm2>


\* <Chime>
chime_go2Stopwatch ==
    /\ status = "Chime"
    /\ pressed["a"]
    /\ status' = "StopWatch"
    /\ UNCHANGED vars_but_status
\* </Chime>


\* <StopWatch>
Stopwatch_go2time ==
    /\ status = "StopWatch"
    /\ pressed["a"]
    /\ status' = "Time"
    /\ UNCHANGED vars_but_status
\* </StopWatch>


\* <Alarms_Beep>
\* </Alarms_Beep>


\* <Helpers>

\* Key presses
PressKey(k) ==
    /\ ~pressed[k] /\ pressed' = [pressed EXCEPT ![k] = TRUE]
    /\ UNCHANGED << light, status, waited_2_min, waited_2_sec >>
ReleaseKey(k) ==
    /\ pressed[k] /\ pressed' = [pressed EXCEPT ![k] = FALSE]
    /\ UNCHANGED << light, status, waited_2_min, waited_2_sec >>

\* Waits
waited_2_min_t == ~waited_2_min /\ waited_2_min' = TRUE
    /\ UNCHANGED << light, status, waited_2_sec, pressed >>
waited_2_min_f == waited_2_min /\ waited_2_min' = FALSE
    /\ UNCHANGED << light, status, waited_2_sec, pressed >>

waited_2_sec_t == ~waited_2_sec /\ waited_2_sec' = TRUE
    /\ UNCHANGED << light, status, waited_2_min, pressed >>
waited_2_sec_f == waited_2_sec /\ waited_2_sec' = FALSE
    /\ UNCHANGED << light, status, waited_2_min, pressed >>
\* </Helpers>


\* <Temporal properties>

(***************************************************************************)
(* I believe the original eventually_time property from Dash expressed in  *)
(* CTL says that "on a press_a, it's possible that in the future the       *)
(* display will display the time".  However, since TLA+'s temporal logic   *)
(* is LTL-based and not CTL, we can't easily express possibility           *)
(* properties.  So, instead, we'll state that "on a press_a, in the future *)
(* the display will display the time".                                     *)
(***************************************************************************)

EventuallyTime ==
    [] (pressed["a"] => <> (status = "Time"))
\* Note: the above property does NOT hold with weak or strong fairness on
\* all the actions on vars

\* </Temporal properties>


\* Spec

Next ==
    \/ light_off_light_on \/ light_on_light_off
    \/ time_show_date \/ time_try_update \/ time_go2alarm1
    \/ date_show_time \/ date_return_to_time
    \/ wait_show_time \/ wait_show_update
    \/ update_show_time
    \/ alarm1_go2alarm2
    \/ alarm2_go2chime
    \/ chime_go2Stopwatch
    \/ Stopwatch_go2time
    \/ \E k \in KEYS: PressKey(k)
    \/ \E k \in KEYS: ReleaseKey(k)
    \/ waited_2_min_t \/ waited_2_min_f
    \/ waited_2_sec_t \/ waited_2_sec_f

Live == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Live  (************************************)
                                       (* every transition either          *)
                                       (* satisfies the action formula     *)
                                       (* `Next' or leaves the expression  *)
                                       (* `vars' unchanged.  In            *)
                                       (* particular, this admits          *)
                                       (* "stuttering transitions" that do *)
                                       (* not affect `vars'.  That is to   *)
                                       (* say, [][Next]_vars == [](Next \/ *)
                                       (* (vars' = vars))                  *)
                                       (************************************) 

=============================================================================
\* Modification History
\* Last modified Wed Oct 27 23:13:23 EDT 2021 by bandali
\* Last modified Tue Jul 17 14:04:48 EDT 2018 by amin
\* Created Tue May 29 18:29:07 EDT 2018 by amin
