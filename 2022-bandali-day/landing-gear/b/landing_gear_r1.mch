/* The Landing Gear case study - B model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Landing Gear B model.

The Landing Gear B model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Landing Gear B model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Landing Gear B model.  If not, see
<https://www.gnu.org/licenses/>.


The Landing Gear management case study is described in
\cite{DBLP:conf/asm/BoniolW14} by Boniol et al.

@inproceedings{DBLP:conf/asm/BoniolW14,
  author    = {Fr{\'{e}}d{\'{e}}ric Boniol and
               Virginie Wiels},
  editor    = {Fr{\'{e}}d{\'{e}}ric Boniol and
               Virginie Wiels and
               Yamine A{\"{\i}}t Ameur and
               Klaus{-}Dieter Schewe},
  title     = {The Landing Gear System Case Study},
  booktitle = {{ABZ} 2014: The Landing Gear Case Study - Case Study Track, Held at
               the 4th International Conference on Abstract State Machines, Alloy,
               B, TLA, VDM, and Z, Toulouse, France, June 2-6, 2014. Proceedings},
  series    = {Communications in Computer and Information Science},
  volume    = {433},
  pages     = {1--18},
  publisher = {Springer},
  year      = {2014},
  url       = {https://doi.org/10.1007/978-3-319-07512-9\_1},
  doi       = {10.1007/978-3-319-07512-9\_1},
  timestamp = {Tue, 07 May 2019 12:19:36 +0200},
  biburl    = {https://dblp.org/rec/conf/asm/BoniolW14.bib},
  bibsource = {dblp computer science bibliography, https://dblp.org}
}

The Landing Gear B model is an adaptation of the AsmetaL one
described in \cite{DBLP:conf/asm/ArcainiGR14} by Arcaini et al.

@inproceedings{DBLP:conf/asm/ArcainiGR14,
  author    = {Paolo Arcaini and
               Angelo Gargantini and
               Elvinia Riccobene},
  editor    = {Fr{\'{e}}d{\'{e}}ric Boniol and
               Virginie Wiels and
               Yamine A{\"{\i}}t Ameur and
               Klaus{-}Dieter Schewe},
  title     = {Modeling and Analyzing Using ASMs: The Landing Gear System Case Study},
  booktitle = {{ABZ} 2014: The Landing Gear Case Study - Case Study Track, Held at
               the 4th International Conference on Abstract State Machines, Alloy,
               B, TLA, VDM, and Z, Toulouse, France, June 2-6, 2014. Proceedings},
  series    = {Communications in Computer and Information Science},
  volume    = {433},
  pages     = {36--51},
  publisher = {Springer},
  year      = {2014},
  url       = {https://doi.org/10.1007/978-3-319-07512-9\_3},
  doi       = {10.1007/978-3-319-07512-9\_3},
  timestamp = {Wed, 29 May 2019 09:35:57 +0200},
  biburl    = {https://dblp.org/rec/conf/asm/ArcainiGR14.bib},
  bibsource = {dblp computer science bibliography, https://dblp.org}
}

This model has appeared in the following publications:

TODO

*/


MACHINE landing_gear

SETS
	HANDLE_STATUS = {up, down};
	DOOR_STATUS = {closed, opening, open, closing};
	GEAR_STATUS = {retracted, extending, extended, retracting};
	CYLINDER_STATUS = {cylinder_retracted, cylinder_extending,
			   cylinder_extended, cylinder_retracting}

VARIABLES
	handle, doors, gears,
	general_electro_valve,
	open_doors_electro_valve,
	close_doors_electro_valve,
	retract_gears_electro_valve,
	extend_gears_electro_valve

INVARIANT
	handle: HANDLE_STATUS
	& doors: DOOR_STATUS
	& gears: GEAR_STATUS
	& general_electro_valve: BOOL
	& open_doors_electro_valve: BOOL
	& close_doors_electro_valve: BOOL
	& retract_gears_electro_valve: BOOL
	& extend_gears_electro_valve: BOOL
	& (gears = extending or gears = retracting) => doors = open
	& doors = closed => (gears = extended or gears = retracted)

DEFINITIONS
/* tried using CASE here, but it would fail with:
! An error occurred (source: parse_error) !
!   expecting: 'END'
*/
	close_door ==
		IF doors = open THEN
			close_doors_electro_valve := TRUE;
			doors := closing
		ELSIF doors = closing THEN
			general_electro_valve := FALSE;
			close_doors_electro_valve := FALSE;
			doors := closed
		ELSIF doors = opening THEN
			close_doors_electro_valve := TRUE;
			open_doors_electro_valve := FALSE;
			doors := closing
		END;

	cylinder_doors ==
		IF doors = open THEN
			cylinder_extended
		ELSIF doors = opening THEN
			cylinder_extending
		ELSIF doors = closing THEN
			cylinder_retracting
		ELSIF doors = closed THEN
			cylinder_retracted
		END;

	cylinder_gears ==
		IF gears = retracted THEN
			cylinder_retracted
		ELSIF gears = extending THEN
			cylinder_extending
		ELSIF gears = extended THEN
			cylinder_extended
		ELSIF gears = retracting THEN
			cylinder_retracting
		END

INITIALISATION
	handle :: HANDLE_STATUS;
	doors := closed;
	gears := extended;
	general_electro_valve := FALSE;
	open_doors_electro_valve := FALSE;
	close_doors_electro_valve := FALSE;
	retract_gears_electro_valve := FALSE;
	extend_gears_electro_valve := FALSE

OPERATIONS
	retraction_sequenece =
		PRE
			handle = up
		THEN
			IF gears /= retracted THEN
				CASE doors OF
					EITHER closed THEN
						general_electro_valve := TRUE;
						open_doors_electro_valve := TRUE;
						doors := opening
					OR closing THEN
						close_doors_electro_valve := FALSE;
						open_doors_electro_valve := TRUE;
						doors := opening
					OR opening THEN
						open_doors_electro_valve := FALSE;
						doors := open
					OR open THEN
						CASE gears OF
							EITHER extended THEN
								retract_gears_electro_valve := TRUE;
								gears := retracting
							OR retracting THEN
								retract_gears_electro_valve := FALSE;
								gears := retracted
							OR extending THEN
								extend_gears_electro_valve := FALSE;
								retract_gears_electro_valve := TRUE;
								gears := retracting
							END // OR
						END // CASE
					END // OR
				END // CASE
			ELSE
				close_door
			END // IF
		END; // PRE

	outgoing_sequence =
		PRE
			handle = down
		THEN
			IF gears /= extended THEN
				CASE doors OF
					EITHER closed THEN
						general_electro_valve := TRUE;
						open_doors_electro_valve := TRUE;
						doors := opening
					OR opening THEN
						open_doors_electro_valve := FALSE;
						doors := open
					OR open THEN
						CASE gears OF
							EITHER retracted THEN
								extend_gears_electro_valve := TRUE;
								gears := extending
							OR extending THEN
								extend_gears_electro_valve := FALSE;
								gears := extended
							OR retracting THEN
								extend_gears_electro_valve := TRUE;
								retract_gears_electro_valve := FALSE;
								gears := extending
							END // OR
						END // CASE
					END // OR
				END // CASE
			END // IF
		END; // PRE

	toggle_handle =
		IF handle = up THEN
			handle := down
		ELSE
			handle := up
		END

END
