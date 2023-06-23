# General README about checking properties about Dash models

## Equality?
- currently Snapshots can be different atoms but have the same field values?

## Reachability
- only needed when view instances of the model in tcmc option
(TCMC explored only reachable snapshots for ctl)
- there can be orphan snapshots with reachability but these are other initial states
- 
## Significant scope (# of Snapshots)
- might be less than the number of transitions; might be more
- can this be determined for Electrum and traces methods?
- if takeni is part of the model, the sig scope must be at least the number of transitions + 1

## expect 0/1
- expect 1 means SAT (an instance for run; prop does not hold for check)
- expect 0 meanst UNSAT (no instance for run; prop holds for check)

## Themes
- there is a generic theme in dash-theme.thm
- sometimes a more specific theme is needed to display variables as attributes; such a theme is in the directory with the model