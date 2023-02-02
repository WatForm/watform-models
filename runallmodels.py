#!/usr/local/bin/python3

# make this file executable and run "./runallmodels.py"


# This script runs a binary with options on all models with a certain extension

# CONFIGURATION -----------------------------

# set path toexecutable
exe = "java -jar /Users/nday/UW/github/org.alloytools.alloy/org.alloytools.alloy.dashbuild/target/org.alloytools.alloy.dashbuild.jar"
options = "-m traces"
ext = "-traces.dsh"

# set path to tests to run
# usually either whole archive or one year
locn = "./2022-tamjid-thesis/"

# seconds
uppertimethreshold = 200

stop_on_first_fail = False

# NO CONFIGURATION BELOW THIS LINE ---------------------------

import os
from os.path import isfile, join
import subprocess

import sys
from subprocess import Popen, PIPE, TimeoutExpired

print ("\n++ Running files ...")
cnt = 0
errlist = []

myinputpath = locn
print("Checking files within: "+myinputpath)
print("With extension: " + ext)
if os.path.exists(myinputpath):
    listoffiles = []
    # r=root, d=directories, f = files
    for r, d, f in os.walk(myinputpath):
        for file in f:
            if file.endswith(ext):
                listoffiles.append(os.path.join(r, file))
    listoffiles.sort()
else:
    print("No files to test")
    exit(1)

for filename in listoffiles:
    cnt = cnt + 1
    file_object = open(filename, 'r')
    # parse errors come to stderr
    print("----------------")
    print("Running: "+exe+" "+options + " " + filename)
    with subprocess.Popen(exe+' '+options+' '+"'"+filename+"'", stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True,shell=True) as p:
        try: 
            # output is the output stream from calling george on the file
            (output, err) = p.communicate(timeout=uppertimethreshold)
            rc = p.returncode
            if rc != 0:
                errlist.append(filename)
        except subprocess.TimeoutExpired:
            p.kill()
            (output, err) = p.communicate()
            rc = GEORGE_TIMEOUT
            errlist.append(filename)
        except Exception as ex:
            (output, err) = p.communicate()
            rc = EXCEPTION
            errlist.append(file)
    print(output)
    print(err)    
    if errlist != 0 and stop_on_first_fail:
        break
            
print("** Files executed: " + str(cnt))
if errlist != [] :
    print("** Failures: "+ str(len(errlist)))
    for i in errlist:
        print(i)
