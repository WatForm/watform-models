# README

## Organization

Each model.dsh file is in a directory called 'model'.

Optionally, also present in that directory is a 

model.opt file

which contains any additional options for that model (such as '-single').

Properties with commands are each in a file called 

model-method-propname.ver   

These properties are specific to the model checking method (tcmc, traces, electrum). 

## Step 1: ./run_all_models -t tcmc (or another m/c method) <dir_name>

This python scripts translates all .dsh models present in the directory adding in any options present in model.opt for the method given (default method is `traces`).

(Note: -t is the default for run_all_models)

## Step 2: ./run_all_models -s <dir_name>

Checks .als models in model directories are satisfiable.

## Step 3: ./run_all_models.py -c <dir_name>

Creates .als files of all combinations of the model and properties in the combine_models directory.

## Step 4: ./run_all_models -p <dir_name>

Runs our dashcli on all .als files in combine_models directory and checks which commands do not meet "expectations".

## Step 5: clean up .als files

make clean

## Notes

If dir_name is not provided, it runs over all directories (except combined_files).