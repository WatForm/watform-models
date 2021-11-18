----------------------- MODULE digital_watch_pluscal -----------------------
(* The DigitalWatch case study - PlusCal model

Copyright (c) 2018 Ali Abbassi <aabbassi@uwaterloo.ca>
Copyright (c) 2018 Nancy Day <nday@uwaterloo.ca>
Copyright (c) 2018-2020 Amin Bandali <bandali@uwaterloo.ca>

This file is part of the DigitalWatch PlusCal model.

The DigitalWatch PlusCal model is free software: you can redistribute
it and/or modify it under the terms of the GNU General Public License
as published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The DigitalWatch PlusCal model is distributed in the hope that it will
be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the DigitalWatch PlusCal model.  If not, see
<https://www.gnu.org/licenses/>.


The DigitalWatch case study is described
in~\cite{DBLP:journals/scp/Harel87} by Harel.  The DigitalWatch
PlusCal model is an adaptation of the original model(s) presented
there.

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

DISPLAY == { "Time", "Date", "Wait", "Update"
           , "Alarm1", "Alarm2", "Chime", "StopWatch"
           , "Alarms_Beep" (* doesn't seem to be used right now *)
           }

KEYS == { "a", "b", "c", "d" }

(* --algorithm digital_watch_pluscal
variables light = FALSE,
          display = "Time",
          pressed = [k \in KEYS |-> FALSE],
          waited_2_min = FALSE,
          waited_2_sec = FALSE;

\* <Light>
process light_off_light_on = "light_off_light_on"
begin
  l_off_on:
    if light = FALSE /\ pressed["b"] then
      light := TRUE
    end if
end process

process light_on_light_off = "light_on_light_off"
begin
  l_on_off:
    if light = TRUE /\ ~pressed["b"] then
      light := FALSE
    end if
end process
\* </Light>

\* <Time>
process time_show_date = "time_show_date"
begin
  t_s_d:
    if display = "Time" /\ pressed["d"] then
        display := "Date"
    end if
end process

process time_try_update = "time_try_update"
begin
  t_t_u:
    if display = "Time" /\ pressed["c"] then
        display := "Wait"
    end if
end process

process time_go2alarm1 = "time_go2alarm1"
begin
  t_g2a1:
    if display = "Time" /\ pressed["a"] then
        display := "Alarm1"
    end if
end process
\* </Time>

\* <Date>
process date_show_time = "date_show_time"
begin
  d_s_t:
    if display = "Date" /\ pressed["d"] then
        display := "Time"
    end if
end process

process date_return_to_time = "date_return_to_time"
begin
  d_r_t_t:
    if display = "Date" /\ waited_2_min then
        display := "Time"
    end if
end process
\* </Date>

\* <Wait>
process wait_show_time = "wait_show_time"
begin
  w_s_t:
    if display = "Wait" /\ ~pressed["c"] then
        display := "Time"
    end if
end process

process wait_show_update = "wait_show_update"
begin
  w_s_u:
    if display = "Wait" /\ waited_2_sec then
        display := "Update"
    end if
end process
\* </Wait>

\* <Update>
process update_show_time = "update_show_time"
begin
  u_s_t:
    if display = "Update" /\ pressed["b"] then
        display := "Time"
    end if
end process
\* </Update>

\* <Alarm1>
process alarm1_go2alarm2 = "alarm1_go2alarm2"
begin
  a1_g2a2:
    if display = "Alarm1" /\ pressed["a"] then
        display := "Alarm2"
    end if
end process
\* </Alarm1>

\* <Alarm2>
process alarm2_go2chime = "alarm2_go2chime"
begin
  a2_g2c:
    if display = "Alarm2" /\ pressed["a"] then
        display := "Chime"
    end if
end process
\* </Alarm2>

\* <Chime>
process chime_go2Stopwatch = "chime_go2Stopwatch"
begin
  c_g2s:
    if display = "Chime" /\ pressed["a"] then
        display := "StopWatch"
    end if
end process
\* </Chime>

\* <StopWatch>
process Stopwatch_go2time = "Stopwatch_go2time"
begin
  s_g2t:
    if display = "StopWatch" /\ pressed["a"] then
        display := "Time"
    end if
end process
\* </StopWatch>

\* <Alarms_Beep>
\* </Alarms_Beep>

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES light, display, pressed, waited_2_min, waited_2_sec, pc

vars == << light, display, pressed, waited_2_min, waited_2_sec, pc >>

ProcSet == {"light_off_light_on"} \cup {"light_on_light_off"} \cup {"time_show_date"} \cup {"time_try_update"} \cup {"time_go2alarm1"} \cup {"date_show_time"} \cup {"date_return_to_time"} \cup {"wait_show_time"} \cup {"wait_show_update"} \cup {"update_show_time"} \cup {"alarm1_go2alarm2"} \cup {"alarm2_go2chime"} \cup {"chime_go2Stopwatch"} \cup {"Stopwatch_go2time"}

Init == (* Global variables *)
        /\ light = FALSE
        /\ display = "Time"
        /\ pressed = [k \in KEYS |-> FALSE]
        /\ waited_2_min = FALSE
        /\ waited_2_sec = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "light_off_light_on" -> "l_off_on"
                                        [] self = "light_on_light_off" -> "l_on_off"
                                        [] self = "time_show_date" -> "t_s_d"
                                        [] self = "time_try_update" -> "t_t_u"
                                        [] self = "time_go2alarm1" -> "t_g2a1"
                                        [] self = "date_show_time" -> "d_s_t"
                                        [] self = "date_return_to_time" -> "d_r_t_t"
                                        [] self = "wait_show_time" -> "w_s_t"
                                        [] self = "wait_show_update" -> "w_s_u"
                                        [] self = "update_show_time" -> "u_s_t"
                                        [] self = "alarm1_go2alarm2" -> "a1_g2a2"
                                        [] self = "alarm2_go2chime" -> "a2_g2c"
                                        [] self = "chime_go2Stopwatch" -> "c_g2s"
                                        [] self = "Stopwatch_go2time" -> "s_g2t"]

l_off_on == /\ pc["light_off_light_on"] = "l_off_on"
            /\ IF light = FALSE /\ pressed["b"]
                  THEN /\ light' = TRUE
                  ELSE /\ TRUE
                       /\ light' = light
            /\ pc' = [pc EXCEPT !["light_off_light_on"] = "Done"]
            /\ UNCHANGED << display, pressed, waited_2_min, waited_2_sec >>

light_off_light_on == l_off_on

l_on_off == /\ pc["light_on_light_off"] = "l_on_off"
            /\ IF light = TRUE /\ ~pressed["b"]
                  THEN /\ light' = FALSE
                  ELSE /\ TRUE
                       /\ light' = light
            /\ pc' = [pc EXCEPT !["light_on_light_off"] = "Done"]
            /\ UNCHANGED << display, pressed, waited_2_min, waited_2_sec >>

light_on_light_off == l_on_off

t_s_d == /\ pc["time_show_date"] = "t_s_d"
         /\ IF display = "Time" /\ pressed["d"]
               THEN /\ display' = "Date"
               ELSE /\ TRUE
                    /\ UNCHANGED display
         /\ pc' = [pc EXCEPT !["time_show_date"] = "Done"]
         /\ UNCHANGED << light, pressed, waited_2_min, waited_2_sec >>

time_show_date == t_s_d

t_t_u == /\ pc["time_try_update"] = "t_t_u"
         /\ IF display = "Time" /\ pressed["c"]
               THEN /\ display' = "Wait"
               ELSE /\ TRUE
                    /\ UNCHANGED display
         /\ pc' = [pc EXCEPT !["time_try_update"] = "Done"]
         /\ UNCHANGED << light, pressed, waited_2_min, waited_2_sec >>

time_try_update == t_t_u

t_g2a1 == /\ pc["time_go2alarm1"] = "t_g2a1"
          /\ IF display = "Time" /\ pressed["a"]
                THEN /\ display' = "Alarm1"
                ELSE /\ TRUE
                     /\ UNCHANGED display
          /\ pc' = [pc EXCEPT !["time_go2alarm1"] = "Done"]
          /\ UNCHANGED << light, pressed, waited_2_min, waited_2_sec >>

time_go2alarm1 == t_g2a1

d_s_t == /\ pc["date_show_time"] = "d_s_t"
         /\ IF display = "Date" /\ pressed["d"]
               THEN /\ display' = "Time"
               ELSE /\ TRUE
                    /\ UNCHANGED display
         /\ pc' = [pc EXCEPT !["date_show_time"] = "Done"]
         /\ UNCHANGED << light, pressed, waited_2_min, waited_2_sec >>

date_show_time == d_s_t

d_r_t_t == /\ pc["date_return_to_time"] = "d_r_t_t"
           /\ IF display = "Date" /\ waited_2_min
                 THEN /\ display' = "Time"
                 ELSE /\ TRUE
                      /\ UNCHANGED display
           /\ pc' = [pc EXCEPT !["date_return_to_time"] = "Done"]
           /\ UNCHANGED << light, pressed, waited_2_min, waited_2_sec >>

date_return_to_time == d_r_t_t

w_s_t == /\ pc["wait_show_time"] = "w_s_t"
         /\ IF display = "Wait" /\ ~pressed["c"]
               THEN /\ display' = "Time"
               ELSE /\ TRUE
                    /\ UNCHANGED display
         /\ pc' = [pc EXCEPT !["wait_show_time"] = "Done"]
         /\ UNCHANGED << light, pressed, waited_2_min, waited_2_sec >>

wait_show_time == w_s_t

w_s_u == /\ pc["wait_show_update"] = "w_s_u"
         /\ IF display = "Wait" /\ waited_2_sec
               THEN /\ display' = "Update"
               ELSE /\ TRUE
                    /\ UNCHANGED display
         /\ pc' = [pc EXCEPT !["wait_show_update"] = "Done"]
         /\ UNCHANGED << light, pressed, waited_2_min, waited_2_sec >>

wait_show_update == w_s_u

u_s_t == /\ pc["update_show_time"] = "u_s_t"
         /\ IF display = "Update" /\ pressed["b"]
               THEN /\ display' = "Time"
               ELSE /\ TRUE
                    /\ UNCHANGED display
         /\ pc' = [pc EXCEPT !["update_show_time"] = "Done"]
         /\ UNCHANGED << light, pressed, waited_2_min, waited_2_sec >>

update_show_time == u_s_t

a1_g2a2 == /\ pc["alarm1_go2alarm2"] = "a1_g2a2"
           /\ IF display = "Alarm1" /\ pressed["a"]
                 THEN /\ display' = "Alarm2"
                 ELSE /\ TRUE
                      /\ UNCHANGED display
           /\ pc' = [pc EXCEPT !["alarm1_go2alarm2"] = "Done"]
           /\ UNCHANGED << light, pressed, waited_2_min, waited_2_sec >>

alarm1_go2alarm2 == a1_g2a2

a2_g2c == /\ pc["alarm2_go2chime"] = "a2_g2c"
          /\ IF display = "Alarm2" /\ pressed["a"]
                THEN /\ display' = "Chime"
                ELSE /\ TRUE
                     /\ UNCHANGED display
          /\ pc' = [pc EXCEPT !["alarm2_go2chime"] = "Done"]
          /\ UNCHANGED << light, pressed, waited_2_min, waited_2_sec >>

alarm2_go2chime == a2_g2c

c_g2s == /\ pc["chime_go2Stopwatch"] = "c_g2s"
         /\ IF display = "Chime" /\ pressed["a"]
               THEN /\ display' = "StopWatch"
               ELSE /\ TRUE
                    /\ UNCHANGED display
         /\ pc' = [pc EXCEPT !["chime_go2Stopwatch"] = "Done"]
         /\ UNCHANGED << light, pressed, waited_2_min, waited_2_sec >>

chime_go2Stopwatch == c_g2s

s_g2t == /\ pc["Stopwatch_go2time"] = "s_g2t"
         /\ IF display = "StopWatch" /\ pressed["a"]
               THEN /\ display' = "Time"
               ELSE /\ TRUE
                    /\ UNCHANGED display
         /\ pc' = [pc EXCEPT !["Stopwatch_go2time"] = "Done"]
         /\ UNCHANGED << light, pressed, waited_2_min, waited_2_sec >>

Stopwatch_go2time == s_g2t

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == light_off_light_on \/ light_on_light_off \/ time_show_date
           \/ time_try_update \/ time_go2alarm1 \/ date_show_time
           \/ date_return_to_time \/ wait_show_time \/ wait_show_update
           \/ update_show_time \/ alarm1_go2alarm2 \/ alarm2_go2chime
           \/ chime_go2Stopwatch \/ Stopwatch_go2time
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeOK ==  \* Typing invariant
    /\ light \in BOOLEAN  \* FALSE: Off, TRUE: On
    /\ display \in DISPLAY
    /\ pressed \in [KEYS -> BOOLEAN]
    /\ waited_2_min \in BOOLEAN
    /\ waited_2_sec \in BOOLEAN

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
    [] (pressed["a"] => <> (display = "Time"))
\* Note: the above property does NOT hold with weak or strong fairness on
\* all the actions on vars

Live == WF_vars(Next)

\* </Temporal properties>

=============================================================================
\* Modification History
\* Last modified Wed Oct 27 22:56:16 EDT 2021 by bandali
\* Created Tue Dec 17 16:15:32 EST 2019 by bandali
