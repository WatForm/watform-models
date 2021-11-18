/* The EHealth case study - AsmetaL model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the EHealth AsmetaL model.

The EHealth AsmetaL model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The EHealth AsmetaL model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the EHealth AsmetaL model.  If not, see
<https://www.gnu.org/licenses/>.


The EHealth case study is described in Prof. Jonathan S. Ostroff's
technical report~\cite{ostroff2017} and used for teaching EECS 4312,
the Software Engineering Requirements course, at York University,
Toronto, Canada.

@techreport{ostroff2017,
  author      = {Jonathan S. Ostroff},
  title       = {Validating Software via Abstract State Specifications},
  year        = {2017},
  number      = {EECS-2017-02},
  institution = {York University},
  url         = {http://www.eecs.yorku.ca/research/techreports/2017/?abstract=EECS-2017-02}
}

The EHealth AsmetaL model is an adaptation of the TLA+ one by Bandali,
itself based on the snippets presented by
Prof. Ostroff~\cite{ostroff2017}.

This model has appeared in the following publications:

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

asm ehealth

import StandardLibrary

signature:
    enum domain RuleId = {ADD_PATIENT
                        | ADD_MEDICATION
                        | ADD_INTERACTION
                        | ADD_PRESCRIPTION
                        | REMOVE_INTERACTION
                        | REMOVE_PRESCRIPTION}
    enum domain Patients = {PP1 | PP2 | PP3}
    enum domain Medications = {MM1 | MM2 | MM3}

    controlled patients: Patients -> Boolean
    controlled medications: Medications -> Boolean
    controlled interactions: Prod(Medications, Medications) -> Boolean
    controlled prescriptions: Prod(Patients, Medications) -> Boolean

definitions:
    rule r_add_patient($p in Patients) =
        if (not patients($p)) then
            patients($p) := true
        endif

    rule r_add_medication($m in Medications) =
        if (not medications($m)) then
            medications($m) := true
        endif

    rule r_add_interaction($m1 in Medications, $m2 in Medications) =
        if (medications($m1) and medications($m2)
                and $m1 != $m2
                and not (exist $p in Patients with (prescriptions($p, $m1)
                                                or  prescriptions($p, $m2)))) then
            par
                interactions($m1, $m2) := true
                interactions($m2, $m1) := true
            endpar
        endif

    rule r_add_prescription($p in Patients, $m in Medications) =
        if (patients($p) and medications($m)
                and not prescriptions($p, $m)
                and not (exist $m0 in Medications with (prescriptions($p, $m0)
                                                    and interactions($m, $m0)))) then
            prescriptions($p, $m) := true
        endif

    rule r_remove_interaction($m1 in Medications, $m2 in Medications) =
        if (medications($m1) and medications($m2) and interactions($m1, $m2)) then
            par
                interactions($m1, $m2) := false
                interactions($m2, $m1) := false
            endpar
        endif

    rule r_remove_prescription($p in Patients, $m in Medications) =
        if (patients($p) and medications($m) and prescriptions($p, $m)) then
            prescriptions($p, $m) := false
        endif

    invariant over interactions:
        (forall $m1 in Medications, $m2 in Medications
            with (medications($m1) and medications($m2) and interactions($m1, $m2))
            implies interactions($m2, $m1))

    invariant over interactions:
        (forall $m in Medications with medications($m) implies not interactions($m, $m))

    invariant over prescriptions:
        (forall $m1 in Medications, $m2 in Medications, $p in Patients
            with (medications($m1) and medications($m2) and patients($p)
                    and interactions($m1, $m2))
            implies not (prescriptions($p, $m1) and prescriptions($p, $m2)))

    main rule r_Main =
        choose $p in Patients, $m1 in Medications, $m2 in Medications, $rule in RuleId with true do
            switch($rule)
                case ADD_PATIENT:
                    r_add_patient[$p]
                case ADD_MEDICATION:
                    r_add_medication[$m1]
                case ADD_INTERACTION:
                    r_add_interaction[$m1, $m2]
                case ADD_PRESCRIPTION:
                    r_add_prescription[$p, $m1]
                case REMOVE_INTERACTION:
                    r_remove_interaction[$m1, $m2]
                case REMOVE_PRESCRIPTION:
                    r_remove_prescription[$p, $m1]
            endswitch

default init s0:
    function patients($p in Patients) = false
    function medications($m in Medications) = false
    function interactions($m1 in Medications, $m2 in Medications) = false
    function prescriptions($p in Patients, $m in Medications) = false
