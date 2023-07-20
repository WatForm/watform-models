------------------------------ MODULE ehealth ------------------------------
(* The EHealth case study - TLA+ model

Copyright (c) 2017 Jonathan Ostroff <jonathan@yorku.ca>
Copyright (c) 2017-2020 Amin Bandali <bandali@uwaterloo.ca>

This file is part of the EHealth TLA+ model.

The EHealth TLA+ model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The EHealth TLA+ model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the EHealth TLA+ model.  If not, see
<https://www.gnu.org/licenses/>.


The EHealth case study is described in Prof. Jonathan S. Ostroff's
technical report~\cite{ostroff2017} and used for teaching EECS 4312,
the Software Engineering Requirements course, at York University,
Toronto, Canada.  This model is a completed version of the snippets
presented by Prof. Ostroff in the above technical report.

The EHealth case study has appeared in the following publications:

@techreport{ostroff2017,
  author      = {Jonathan S. Ostroff},
  title       = {Validating Software via Abstract State Specifications},
  year        = {2017},
  number      = {EECS-2017-02},
  institution = {York University},
  url         = {http://www.eecs.yorku.ca/research/techreports/2017/?abstract=EECS-2017-02}
}

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

EXTENDS Naturals, Sequences

CONSTANTS
    M \* set of all medications in the universe
  , P \* set of all patients in the universe

VARIABLES
    medications   \* set of medications registered in the system
  , patients      \* set of patients registered in the system
  , prescriptions \* medications prescribed to each patient
  , interactions  \* dangerous interactions

vars == <<medications, patients, prescriptions, interactions>>

TypeOK ==
    /\ patients \subseteq P
    /\ medications \subseteq M
    /\ prescriptions \subseteq patients \X medications
    /\ interactions  \subseteq medications \X medications


add_patient(p) ==
    IF
        /\ p \in P
        /\ p \notin patients
    THEN
        /\ patients' = patients \union {p}
        /\ UNCHANGED <<medications, interactions, prescriptions>>
    ELSE
        UNCHANGED vars

add_medication(m) ==
    IF
        /\ m \in M
        /\ m \notin medications
    THEN
        /\ medications' = medications \union {m}
        /\ UNCHANGED <<patients, interactions, prescriptions>>
    ELSE
        UNCHANGED vars

add_interaction(m1, m2) ==
    IF
        /\ m1 \in medications
        /\ m2 \in medications
        /\ m1 /= m2
        /\ <<m1, m2>> \notin interactions
        /\ \A p \in patients: ~(<<p, m1>> \in prescriptions
                              /\ <<p, m2>> \in prescriptions)
    THEN
        /\ interactions' = interactions \union {<<m1, m2>>, <<m2, m1>>}
        /\ UNCHANGED <<medications, patients, prescriptions>>
    ELSE
        UNCHANGED vars

add_prescription(p, m) ==
    IF
        /\ p \in patients
        /\ m \in medications
        /\ <<p, m>> \notin prescriptions
        /\ \A x \in medications: <<p, x>> \in prescriptions =>
            <<x, m>> \notin interactions
    THEN
        /\ prescriptions' = prescriptions \union {<<p, m>>}
        /\ UNCHANGED <<medications, patients, interactions>>
    ELSE
        UNCHANGED vars

remove_interaction(m1, m2) ==
    IF
        /\ m1 \in medications
        /\ m2 \in medications
        /\ <<m1, m2>> \in interactions
    THEN
        /\ interactions' = interactions \ {<<m1, m2>>, <<m2, m1>>}
        /\ UNCHANGED <<medications, patients, prescriptions>>
    ELSE
        UNCHANGED vars

remove_prescription(p, m) ==
    IF
        /\ p \in patients
        /\ m \in medications
        /\ <<p, m>> \in prescriptions
    THEN
        /\ prescriptions' = prescriptions \ {<<p, m>>}
        /\ UNCHANGED <<medications, patients, interactions>>
    ELSE
        UNCHANGED vars


Init ==
    /\ medications = {}
    /\ patients = {}
    /\ prescriptions = {}
    /\ interactions  = {}

Next ==
    \/ \E p \in P: add_patient(p)
    \/ \E m \in M: add_medication(m)
    \/ (\E m1, m2 \in M: add_interaction(m1, m2) \/ remove_interaction(m1, m2))
    \/ (\E m \in M, p \in P: add_prescription(p, m) \/ remove_prescription(p, m))

Spec == Init /\ [][Next]_vars


\* Invariants

Symmetry == \A m1, m2 \in medications:
    <<m1, m2>> \in interactions <=>
    <<m2, m1>> \in interactions

\* a medication does not interact with itself
Irreflexive == \A m \in medications:
    <<m, m>> \notin interactions

\* all prescriptions are safe (no dangerous interactions)
SafePrescriptions ==
    \A m1, m2 \in medications, p \in patients:
        <<m1, m2>> \in interactions =>
            ~(<<p, m1>> \in prescriptions
            /\ <<p, m2>> \in prescriptions)

=============================================================================
\* Modification History
\* Last modified Sun Jul 05 16:15:54 EDT 2020 by bandali
\* Created Thu Nov 09 19:30:33 EST 2017 by bandali
