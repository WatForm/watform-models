# General README about checking properties about Dash models using TCMC

## Methodology

Per model, try Steps 1,2, and 3 on an individual model leaving the .ver (property) file with scopes that take a reasonable amount of time.

Register the information in the ver-notes.csv file.  This file is used in the combinefile.py script to create models that are run as a batch.

## Introduction

Transitive-closure-based Model Checking (TCMC) is a model checking method for CTL properties of Kripke structures implemented in Alloy.  In the translation from Dash to Alloy, the `-m tcmc` option creates an Alloy model suitable for TCMC.

A snapshot (DshSnapshot) is an atom representing a "state" in the Kripke structure.  Relations with the snapshot as the first element of the tuple describe attributes of the state.  We call these attribute relations.  In the Alloy model,

tcmc/ks_s0 = set of DshSnapshots that are initial states
tcmc/ks_sigma = set of pairs of the small step relation

The DshSnapshots must all have a different set of attribute values because of the `allSnapshotsDifferent` fact.  Loops are possible in TCMC instances so this fact makes it easier to understand the instance and DshSnapshots are essentially records (matching other model checking tools).

The `dsh_reachability` predicate included in the run/check, ensures that an instance of the model does not have orphan snapshots. However, any check of ctl_mc (for TCMC) only checks the property for reachable snapshots so dsh_reachability does NOT need to be included in these checks.

File naming convention: model-tcmc-propname.ver

If the command includes `expect 1` it means SAT (an instance for run; property does not hold for check).  `expect 0` means UNSAT (no instance for run; property holds for check).  Pls include an "expect" in all commands.

## Step 1: Explore

The first step is always to look at instances of the model in the GUI.  These instances should only include reachable states and are easier to look at if there is only one initial state (to avoid orphan initial states):

run { 
   #(tcmc/ks_s0) = 1 
   dsh_reachability 
} for 4 Sig1, 3 Sig2, exactly 5 DshSnapshot expect 1

Sig1, etc are user-declared signatures that are important for the size of the model (Patient, Player, etc).  These can have exact of non-exact scope.

The scope for DshSnapshot is the number of snapshots in the model - it can be exact or non-exact depending on how you wish to iterate through models

No other Dash-introduced signatures need to be given scopes in the command.

There is a generic theme for viewing instances in the file dash-theme.thm that can be loaded for viewing instances with the attribute relations as attributes of the DshSnapshot nodes in the graph and with ks_sigma as the only edges in the graph.

Sometimes a more specific theme is needed to display variables as attributes; such a theme is in the directory with the model.

## Step 2: Enough-ops

The significant scope is the # of DshSnapshots needed to create a model in which all transitions are represented in some pair of sigma.  This does not mean that ALL models with this number of snapshots include a representative pair of every transition.

The second step is to run the enough_ops predicate to find the significant scope:

run {
   dsh_reachability
   dsh_enough_operations 
} for exactly 8 DshSnapshot, exactly 4 Players, exactly 3 Chairs 

iterating through exactly 2 DshSnapshot, exactly 3 DshSnapshot etc. until there is a satisfiable model.

The user-introduced signatures should keep their scopes constant through this process.  The significant scope is likely to be specific for the user-introduced signature scope values.

In some models and with some values for user-introduced signature scope values, it can take a very long time to find the significant scope and sometimes it is not possible.

With the transition taken (taken relation attribute) as part of the model, the significant scope must be at least as large as the number of transitions + 1 (the initial state has no transition taken).

## Step 3: Specific Properties

TCMC is used to check CTL properties.  For example:

pred not_light_on_and_off {
    ctl_mc[
        ag[
            { s : DshSnapshot | !(DigitalWatch_Light_Off + DigitalWatch_Light_On in s.dsh_conf0)}
            ]
        ]    
}

check {
	not_light_on_and_off 
}
for exactly 8 DshSnapshot

If there is an invalid property and therefore a counterexample, it is useful to include reachability (and possible only one initial state) to make it easier to understand the instance:

check { 
	reachability => not_light_on_and_off 
} 
for exactly 8 DshSnapshot

Every command must include an 'expect 1' or 'expect 0' at the end. For example:

... for exactly 6 DshSnapshot, exactly 2 Medication, exactly 2 Patient   expect 0

It should use `exactly` for all scopes. DshSnapshot should be listed first followed by user-introduced top-level scopes in alphabetical order.




