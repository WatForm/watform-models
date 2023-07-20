/* The EHealth case study - B model

Copyright (c) 2018 Ali Abbassi <aabbassi@uwaterloo.ca>
Copyright (c) 2018 Nancy Day <nday@uwaterloo.ca>
Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>

This file is part of the EHealth B model.

The EHealth B model is free software: you can redistribute it and/or
modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The EHealth B model is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the EHealth B model.  If not, see
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

The EHealth B model is an adaptation of the TLA+ one by Bandali,
itself based on the snippets presented by
Prof. Ostroff~\cite{ostroff2017}.

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

MACHINE ehealth

SETS
    Patient; Medication

VARIABLES
    prescriptions, interactions, patients, medications

INVARIANT
    patients : POW(Patient) &
    medications : POW(Medication) &
    interactions : Medication +-> POW(Medication) &
    prescriptions : Patient +-> POW(Medication) &
    !(m1, m2).(m1 : Medication & m2 : Medication =>
        m1 : interactions(m2) => m2 : interactions(m1)) &
    !(med).(med : Medication => not(med : interactions(med))) &
    !(m1, m2, pat).(m1 : Medication & m2 : Medication & pat : Patient =>
        m1 : prescriptions(pat) & m2 : prescriptions(pat) =>
            not(m1 : interactions(m2)))


INITIALISATION
    patients, medications, interactions, prescriptions := {}, {}, {}, {}

OPERATIONS
    addPatient(pat) =
    PRE
        pat : Patient & pat /: patients
    THEN
        patients := patients \/ {pat};
        prescriptions := prescriptions \/ {pat |-> {}}
    END;

    addMedication(med) =
    PRE
        med : Medication & med /: medications
    THEN
        medications := (medications \/ {med});
        interactions := interactions \/ {med |-> {}}
    END;

    addInteraction(m1, m2) =
    PRE
        m1 : medications & m2 : medications & m1 /= m2 & m1 /: interactions(m2)
    THEN
        interactions := interactions <+ {m1 |-> (interactions(m1) \/ {m2})} ;
        interactions := interactions <+ {m2 |-> (interactions(m2) \/ {m1})}
    END;

    addPrescription(pat, med) =
    PRE
        pat : patients & med /: prescriptions(pat) &
            !(m1).(m1 : prescriptions(pat) => med /: interactions(m1))
    THEN
        prescriptions := prescriptions <+ {pat |-> (prescriptions(pat) \/ {med})}
    END;

    removeInteraction(m1, m2) =
    PRE
        m1 : medications & m2 : medications & m1 : interactions(m2)
    THEN
        interactions := interactions <+ {m1 |-> interactions(m1) - {m2}} ;
        interactions := interactions <+ {m2 |-> interactions(m2) - {m1}}
    END;

    removePrescription(pat, med) =
    PRE
        pat : patients & med : medications & med : prescriptions(pat)
    THEN
        prescriptions := prescriptions <+ {pat |-> (prescriptions(pat) - {med})}
    END

END
