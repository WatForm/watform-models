#!/usr/local/bin/python3

# make this file executable and run "./runallmodels.py"
  

# This script runs a binary with options on all models with a certain extension

# CONFIGURATION -----------------------------

# set path toexecutable
exe = "java -cp /Users/nday/UW/github/org.alloytools.alloy/org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar ca.uwaterloo.watform.dash4whole.Dash"
options = "-t -m traces"
#ext = "-tcmc.dsh"
ext = ".als"

# set path to tests to run
# usually either whole archive or one year
locn = "./"

# seconds
uppertimethreshold = 200

stop_on_first_fail = False

# output/err won't be printed
quiet = False 

# NO CONFIGURATION BELOW THIS LINE ---------------------------

import os
from os.path import isfile, join
import subprocess

import sys
from subprocess import Popen, PIPE, TimeoutExpired

print ("\n++ Running files ...")
cnt = 0
errlist = []
sat = 0

myinputpath = locn
print("Checking files within: "+myinputpath)
print("With options: "+options)
print("With extension: " + ext)
if os.path.exists(myinputpath):
    listoffiles = []
    # r=root, d=directories, f = files
    for r, d, f in os.walk(myinputpath):
        for file in f:
            if ext == "" or file.endswith(ext):
                listoffiles.append(os.path.join(r, file))
    listoffiles.sort()
else:
    print("No files to test")
    exit(1)

for filename in listoffiles:
    cnt = cnt + 1
    file_object = open(filename, 'r')
    msg = ""
    # parse errors come to stderr
    if not quiet:
        print("----------------")
        print("Running: "+exe+" "+options + " " + filename)
    with subprocess.Popen(exe+' '+options+' '+"'"+filename+"'", stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True,shell=True) as p:
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
    if errlist != 0 and stop_on_first_fail:
        break
            
print("** Files executed: " + str(cnt))
if ext == ".als":
    print("** SAT result: " + str(sat))
if errlist != [] :
    print("** Failures: "+ str(len(errlist)))
    for i in errlist:
        print(i)
