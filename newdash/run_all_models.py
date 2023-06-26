#!/usr/local/bin/python3

# make this file executable and run "./runallmodels.py"
  
# This script runs a binary with options on all models with a certain extension

# CONFIGURATION -----------------------------

# set path to executable
exe = "java -cp /Users/nday/UW/github/org.alloytools.alloy/org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar ca.uwaterloo.watform.dash4whole.Dash"
#exe = "dashcli"
#options = "-t -m tcmc"
#ext = ".als"

# seconds
uppertimethreshold = 200

stop_on_first_fail = False

# output/err won't be printed
quiet = False 

# NO CONFIGURATION BELOW THIS LINE ---------------------------

import os
from os.path import isfile, join
import subprocess
import argparse
import pathlib
import sys
from subprocess import Popen, PIPE, TimeoutExpired

# dash model filenames are names model.dsh
# which produce model-method.als
# property file names are model-method-propname.ver

# combine only works now for tcmc method

PROP_SUFFIX = '.ver'
METHOD_SUFFIX = '-tcmc.als'
DEFAULT_DEST = 'combined-files'
#DEST_FOLDER_NAME = 'combined-files'
TCMC = 'tcmc'

# copied from Owen's code
# traces are all the .ver files
def combine_files(verfiles):
    tcmcverfiles = list(filter(lambda name: TCMC in name, verfiles))
    for property_file_name in tcmcverfiles:
        print('Found property file:', property_file_name)

        # verfile name is model-tcmc-propname.ver
        # chop to model-tcmc
        parts = property_file_name.split(TCMC) 
        model_file_name = parts[0] +TCMC+".als"

        # change property file name to get .als extension
        parts = property_file_name.split("/")
        x = parts[-1]
        xparts = x.split('.')
        target_file_name = DEFAULT_DEST + "/" + xparts[0] + ".als"
 
        print('    Writing to', target_file_name)
        with open(target_file_name, 'w') as target_file:
            with open(model_file_name, 'r') as model_file:
                for line in model_file:
                    target_file.write(line)

            target_file.write('/* P R O P E R T Y */\n')
            with open(property_file_name, 'r') as property_file:
                for line in property_file:
                    target_file.write(line)

parser = argparse.ArgumentParser(
    description="Translates .dsh files or runs .als files"
)

parser.add_argument('-t', '--translate', nargs='?', choices=['tcmc', 'traces', 'electrum'])

parser.add_argument('-s', '--satisfiable', action='store_true', help='check .als file in model directory is satisfiable')

parser.add_argument('-c', '--combine', action='store_true', help='combine .als and .ver combinations into combined-files directory')

parser.add_argument('-p', '--propertycheck', action='store_true', help='run .als files in combined-files directory for expectations')

parser.add_argument('sources', nargs='*',
                    type=pathlib.Path,
                    default=['2022-bandali-day', '2022-bandali-thesis', '2019-serna-thesis', '2022-tamjid-thesis']
                    )


args = parser.parse_args()
sources = args.sources

args = parser.parse_args()


print ("\n++ Running files ...")
cnt = 0
errlist = []
sat = 0
unsatlist = []
correct = 0;
incorrect = 0;
noexpect = 0;
incorrectlist = []
noexpectlist = []


translate = args.translate

# precedence of tasks here if multiple options given on command line
if translate != None:
    task = 'translate'
    options = '-t -m '+ translate
    ext = ".dsh"
elif args.satisfiable:
    task = 'satisfiable'
    options = ""
    ext = ".als"
elif args.combine:
    task = 'combine'
    options = ""
    ext = ".ver"
elif args.propertycheck:
    task = 'propertycheck'
    sources = ["combined-files"]
    options = ""
    ext = ".als"
else:
    print("No options provided so nothing to do!")
    exit(1)


print("With options: "+options)
print("With extension: " + ext)

for source in sources:
    print('Searching source:', source)

    listoffiles = []
    for root, dirs, files in os.walk(source):
        if 'combined-files' in dirs:  # skip the combined-files folder
            dirs.remove('combined-files')
        for file in files:
            fragment_path = str(os.path.join(root, file))
            listoffiles.append(fragment_path)


    allfiles = list(filter(lambda name: name.endswith(ext), listoffiles))

    if task == 'combine':
        combine_files(allfiles)
        exit(0)

    for filename in allfiles:
        cnt = cnt + 1
        file_object = open(filename, 'r')
        msg = ""
        if (args.translate):
            parts = filename.split('.')
            opt_file_name = parts[0] + ".opt"
            if os.path.exists(opt_file_name):
                f = open(opt_file_name,"r")
                options = options + " " + f.readline()  

        # parse errors come to stderr
        cmd = exe+' '+options+' '+"'"+filename+"'"
        if not quiet:
            print("----------------")
            print("Running: " + cmd)
        with subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True,shell=True) as p:
            try: 
                # output is the output stream from calling george on the file
                (output, err) = p.communicate(timeout=uppertimethreshold)
                rc = p.returncode
                if rc != 0 and not(filename.endswith("-error.dsh")):
                    errlist.append(filename)
            except subprocess.TimeoutExpired:
                p.kill()
                (output, err) = p.communicate()
                rc = p.returncode
                errlist.append(filename)
                msg = "Timeout"
            except Exception as ex:
                (output, err) = p.communicate()
                rc = p.returncode
                if not(filename.endswith("-error.dsh")):
                    errlist.append(filename)
                    msg = "Exception"
        if not quiet:
            print(output)
            # print(err)  
            # remove the silly error message
            for l in err.splitlines():
                if not(l.startswith("SLF4J:")):
                    print(l)        
            print("Return code: " + str(rc))  
            if msg != "":
                print("Msg: "+ msg)
        if "Result: SAT" in output:
            sat = sat + 1
        else:
            unsatlist.append(filename)
        if "CORRECT" in output:
            correct = correct + 1
        elif "INCORRECT" in output:
            incorrect = incorrect + 1
            incorrectlist.append(filename)
        else:
            noexpect = noexpect + 1
            noexpectlist.append(filename)
        if errlist != 0 and stop_on_first_fail:
            break
            
print("** Files executed: " + str(cnt))
if translate!=None and errlist != [] :
    print("** Failures in translation: "+ str(len(errlist)))
    for i in errlist:
        print(i)
if args.satisfiable:
    print("** SAT #: " + str(sat))
    print("** UNSAT: ")
    for i in unsatlist:
        print(i)
if args.propertycheck:
    print("** CORRECT #:" + str(correct))
    print("** INCORRECT: ")
    for i in incorrectlist:
        print(i)   
    print("** NO EXPECT: ")
    for i in noexpectlist:
        print(i)       
