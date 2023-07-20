/* The DigitalWatch case study - AsmetaL model

Copyright (c) 2018 Jose Serna <jserna@uwaterloo.ca>
Copyright (c) 2018 Nancy Day <nday@uwaterloo.ca>
Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>

This file is part of the DigitalWatch AsmetaL model.

The DigitalWatch AsmetaL model is free software: you can redistribute
it and/or modify it under the terms of the GNU General Public License
as published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The DigitalWatch AsmetaL model is distributed in the hope that it will
be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the DigitalWatch AsmetaL model.  If not, see
<https://www.gnu.org/licenses/>.


The DigitalWatch case study is described
in~\cite{DBLP:journals/scp/Harel87} by Harel.  The DigitalWatch
AsmetaL model is an adaptation of the original model(s) presented
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

*/

asm digital_watch

import StandardLibrary
import CTLlibrary

signature:
	// domains
	enum domain RuleId = {LIGHT_OFF_LIGHT_ON
						| LIGHT_ON_LIGHT_OFF
						| TIME_SHOW_DATE
						| TIME_TRY_UPDATE
						| TIME_GO2ALARM1
						| DATE_SHOW_TIME
						| DATE_RETURN_TO_TIME
						| WAIT_SHOW_TIME
						| WAIT_SHOW_UPDATE
						| UPDATE_SHOW_TIME
						| ALARM1_GO2ALARM2
						| ALARM2_GO2CHIME
						| CHIME_GO2STOPWATCH
						| STOPWATCH_GO2TIME}
	enum domain Key = {KEY_A | KEY_B | KEY_C | KEY_D}
	enum domain Display = {TIME | DATE  | WAIT | UPDATE
						| ALARM1 | ALARM2 | CHIME
						| STOPWATCH | ALARMS_BEEP}

	// functions
	monitored pressed: Key -> Boolean
	monitored waited_2_min: Boolean
	monitored waited_2_sec: Boolean

	controlled light: Boolean
	controlled display: Display

definitions:

	rule r_light_off_light_on =
		if (not light and pressed(KEY_B)) then
			light := true
		endif

	rule r_light_on_light_off =
		if (light and not pressed(KEY_B)) then
			light := false
		endif

	rule r_time_show_date =
		if (display = TIME and pressed(KEY_D)) then
			display := DATE
		endif

	rule r_time_try_update =
		if (display = TIME and pressed(KEY_C)) then
			display := WAIT
		endif

	rule r_time_go2alarm1 =
		if (display = TIME and pressed(KEY_A)) then
			display := ALARM1
		endif

	rule r_date_show_time =
		if (display = DATE and pressed(KEY_D)) then
			display := TIME
		endif

	rule r_date_return_to_time =
		if (display = DATE and waited_2_min) then
			display := TIME
		endif

	rule r_wait_show_time =
		if (display = WAIT and not pressed(KEY_C)) then
			display := TIME
		endif

	rule r_wait_show_update =
		if (display = WAIT and waited_2_sec) then
			display := UPDATE
		endif

	rule r_update_show_time =
		if (display = UPDATE and pressed(KEY_B)) then
			display := TIME
		endif

	rule r_alarm1_go2alarm2 =
		if (display = ALARM1 and pressed(KEY_A)) then
			display := ALARM2
		endif

	rule r_alarm2_go2chime =
		if (display = ALARM2 and pressed(KEY_A)) then
			display := CHIME
		endif

	rule r_chime_go2stopwatch =
		if (display = CHIME and pressed(KEY_A)) then
			display := STOPWATCH
		endif

	rule r_stopwatch_go2time =
		if (display = STOPWATCH and pressed(KEY_A)) then
			display := TIME
		endif

	invariant over display:
		pressed(KEY_A) implies ef(ex(display = TIME))

	main rule r_Main =
		choose $rule in RuleId with true do
			switch($rule)
				case LIGHT_OFF_LIGHT_ON:
					r_light_off_light_on[]
				case LIGHT_ON_LIGHT_OFF:
					r_light_on_light_off[]
				case TIME_SHOW_DATE:
					r_time_show_date[]
				case TIME_TRY_UPDATE:
					r_time_try_update[]
				case TIME_GO2ALARM1:
					r_time_go2alarm1[]
				case DATE_SHOW_TIME:
					r_date_show_time[]
				case DATE_RETURN_TO_TIME:
					r_date_return_to_time[]
				case WAIT_SHOW_TIME:
					r_wait_show_time[]
				case WAIT_SHOW_UPDATE:
					r_wait_show_update[]
				case UPDATE_SHOW_TIME:
					r_update_show_time[]
				case ALARM1_GO2ALARM2:
					r_alarm1_go2alarm2[]
				case ALARM2_GO2CHIME:
					r_alarm2_go2chime[]
				case CHIME_GO2STOPWATCH:
					r_chime_go2stopwatch[]
				case STOPWATCH_GO2TIME:
					r_stopwatch_go2time[]
			endswitch

default init s0:
	function light = false
	function display = TIME
