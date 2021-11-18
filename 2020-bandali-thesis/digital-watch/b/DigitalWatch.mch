/* The DigitalWatch case study - B model

Copyright (c) 2018 Jose Serna <jserna@uwaterloo.ca>
Copyright (c) 2018 Nancy Day <nday@uwaterloo.ca>
Copyright (c) 2018 Ali Abbassi <aabbassi@uwaterloo.ca>
Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>

This file is part of the DigitalWatch B model.

The DigitalWatch B model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The DigitalWatch B model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the DigitalWatch B model.  If not, see
<https://www.gnu.org/licenses/>.


The DigitalWatch case study is described
in~\cite{DBLP:journals/scp/Harel87} by Harel.  The DigitalWatch B
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

MACHINE DigitalWatch

SETS
	Light = {lightOn, lightOff};
	Beep = {beepOn, beepOff};
	Display = {time, date, wait, update, alarm1, alarm2, chime, stopwatch};
	ButtonA = {aPressed, aReleased};
	ButtonB = {bPressed, bReleased};
	ButtonC = {cPressed, cReleased};
	ButtonD = {dPressed, dReleased}

VARIABLES
	LightState, BeepState, DisplayState, ButtonAState,
		ButtonBState, ButtonCState, ButtonDState, Waited
	
INVARIANT
	LightState : Light & BeepState : Beep & DisplayState : Display &
		ButtonAState : ButtonA & ButtonBState : ButtonB & 
		ButtonCState : ButtonC & ButtonDState : ButtonD & Waited : BOOL &
		!(ba, bb, bc, bd). (ba: ButtonA & bb: ButtonB & bc: ButtonC & bd: ButtonD =>
			ba = aPressed => bb = bReleased & bc = cReleased & bd = dReleased) &
		!(ba, bb, bc, bd). (ba: ButtonA & bb: ButtonB & bc: ButtonC & bd: ButtonD =>
			ba = aPressed => bb = bReleased & bc = cReleased & bd = dReleased) &
		!(ba, bb, bc, bd). (ba: ButtonA & bb: ButtonB & bc: ButtonC & bd: ButtonD =>
			ba = aPressed => bb = bReleased & bc = cReleased & bd = dReleased) &
		!(ba, bb, bc, bd). (ba: ButtonA & bb: ButtonB & bc: ButtonC & bd: ButtonD =>
			ba = aPressed => bb = bReleased & bc = cReleased & bd = dReleased)
	
INITIALISATION
	LightState, BeepState, DisplayState, ButtonAState,
		ButtonBState, ButtonCState, ButtonDState, Waited :=
		lightOff, beepOff, time, aReleased, bReleased, cReleased, dReleased, FALSE

OPERATIONS
	LightOn =
	PRE
		LightState = lightOff & ButtonBState = bPressed
	THEN
		LightState := lightOn
	END;
	
	LightOff = 
	PRE
		LightState = lightOn & ButtonBState = bReleased
	THEN
		LightState := lightOff
	END;
	
	ShowDate =
	PRE
		DisplayState = time & ButtonDState = dPressed
	THEN
		DisplayState := date || ButtonDState := dReleased
	END;
	
	TryUpdate = 
	PRE
		DisplayState = time & ButtonCState = cPressed & Waited = TRUE
	THEN
		DisplayState := update || ButtonCState := cReleased || Waited := FALSE
	END;
	
	GoToAlarm =
	PRE
		DisplayState = time & ButtonAState = aPressed
	THEN
		DisplayState := date || ButtonAState := aReleased
	END;
	
	ShowTime =
	PRE
		DisplayState = date & ButtonDState = dPressed
	THEN
		DisplayState := time || ButtonDState := dReleased
	END;
	
	ReturnToTime =
	PRE
		DisplayState = date & Waited = TRUE
	THEN
		DisplayState := time || Waited := FALSE
	END;
	
	ShowTimeW =
	PRE
		DisplayState = wait & ButtonCState = cPressed
	THEN
		DisplayState := time || ButtonCState := cReleased
	END;
	
	ShowUpdate =
	PRE
		DisplayState = wait & Waited = TRUE
	THEN
		DisplayState := update || Waited := FALSE
	END;
	
	ShowTimeU = 
	PRE
		DisplayState = update & ButtonBState = bPressed
	THEN
		DisplayState := time || ButtonBState := bReleased
	END;
	
	GoToAlarm2 =
	PRE
		DisplayState = alarm1 & ButtonAState = aPressed
	THEN
		DisplayState := alarm2 || ButtonAState := aReleased
	END;
	
	GoToChime =
	PRE
		DisplayState = alarm2 & ButtonAState = aPressed
	THEN
		DisplayState := chime || ButtonAState := aReleased
	END;
	
	GoToStopwatch =
	PRE
		DisplayState = chime & ButtonAState = aPressed
	THEN
		DisplayState := stopwatch || ButtonAState := aReleased
	END;
	
	GoToTimeS =
	PRE
		DisplayState = stopwatch & ButtonAState = aPressed
	THEN
		DisplayState := time || ButtonAState := aReleased
	END
	
	
	
END
