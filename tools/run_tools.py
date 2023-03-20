#!/usr/bin/python3

#####################################################################################
# Copyright (c) 2023 Randal E. Bryant, Carnegie Mellon University
# Last edit: March 20, 2023
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
# associated documentation files (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge, publish, distribute,
# sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all copies or
# substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
# NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
# OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
########################################################################################

# Run model counting program on benchmark file
# Use newer versions of programs

import getopt
import sys
import os.path
import subprocess
import datetime
import time

def usage(name):
    print("Usage: %s [-h] [-1] [-f] [-s n|g|c] [-m] [-L] [-G] [-F] FILE.EXT ..." % name)
    print("  -h       Print this message")
    print("  -f       Force regeneration of all files")
    print("  -s n|g|c Stop after NNF generation, CRAT generation (g) or proof check (c)")
    print("  -1       Generate one-sided proof (don't validate assertions)")
    print("  -m       Monolithic mode: Do validation with single call to SAT solver")
    print("  -L       Expand each node, rather than using lemmas")
    print("  -G       Prove each literal separately, rather than grouping into single proof")
    print("  -F       Run Lean checker to formally check")
    print("  EXT      Can be any extension for wild-card matching (e.g., cnf, nnf)")

# Blocking file.  If present in directory, won't proceed.  Recheck every sleepTime seconds
blockPath = "./block.txt"
sleepTime = 60

# Defaults
standardTimeLimit = 60

oneSided = False
monolithic = False
useLemma = True
group = True
useLean = False

# Pathnames
d4Program = "d4"

genHome = "../src"
genProgram = genHome + "/cratify"

checkHome = "../src"
checkProgram = checkHome + "/crat-check"

leanHome =  "../lean4"
leanCheckProgram = leanHome + "/ProofChecker/build/bin/checker"

interpreter = "python3"
countHome = "../tools"
countProgram = countHome + "/count-crat.py"

timeLimits = { "D4" : 4000, "GEN" : 10000, "FCHECK" : 1000, "LCHECK" : 4000, "COUNT" : 4000 }

clauseLimit = (1 << 31) - 1

commentChar = 'c'

def waitWhileBlocked():
    first = True
    while os.path.exists(blockPath):
        if first:
            print("Waiting to unblock")
        first = False
        time.sleep(sleepTime)

def checkFile(prefix, fname, logFile):
    f = open(fname, 'r')
    bytes = 0
    lines = 0
    for line in f:
        if len(line) > 0 and line[0] == commentChar:
            continue
        bytes += len(line)
        lines += 1
    print("%s: LOG: size %s %d lines %d bytes" % (prefix, fname, lines, bytes))
    logFile.write("%s: LOG: size %s %d lines %d bytes\n" % (prefix, fname, lines, bytes))
    f.close()

def runProgram(prefix, root, commandList, logFile, extraLogName = None):
    if prefix in timeLimits:
        timeLimit = timeLimits[prefix]
    else:
        timeLimit = standardTimeLimit
    result = ""
    cstring = " ".join(commandList)
    print("%s. %s: Running '%s' with time limit of %d seconds" % (root, prefix, cstring, timeLimit))
    logFile.write("%s LOG: Running %s\n" % (prefix, cstring))
    logFile.write("%s LOG: Time limit %d seconds\n" % (prefix, timeLimit))
    start = datetime.datetime.now()
    try:
        cp = subprocess.run(commandList, capture_output = True, timeout=timeLimit, text=True)
    except subprocess.TimeoutExpired as ex:
        # Incorporate information recorded by external logging
        if (extraLogName is not None):
            try:
                xlog = open(extraLogName, "r")
                for line in xlog:
                    logFile.write(line)
                xlog.close()
            except:
                pass
        print("%s. %s Program timed out after %d seconds" % (root, prefix, timeLimit))
        result += "%s ERROR: Timeout after %d seconds\n" % (prefix, timeLimit)
        delta = datetime.datetime.now() - start
        seconds = delta.seconds + 1e-6 * delta.microseconds
        result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
        result += "%s OUTCOME: Timeout\n" % (prefix)
        logFile.write(result)
        return False
    ok = True
    if cp.returncode != 0:
        result += "%s ERROR: Return code = %d\n" % (prefix, cp.returncode)
        ok = False
    outcome = "normal" if ok else "failed"
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
    result += "%s OUTCOME: %s\n" % (prefix, outcome)
    print("%s. %s: OUTCOME: %s" % (root, prefix, outcome))
    print("%s. %s: Elapsed time: %.3f seconds" % (root, prefix, seconds))
    logFile.write(cp.stdout)
    logFile.write(result)
    return ok

# Only run D4 if don't yet have .nnf file
def runD4(root, home, logFile, force):
    cnfName = home + "/" + root + ".cnf"
    nnfName = home + "/" + root + ".nnf"
    if not force and os.path.exists(nnfName):
        return True
    cmd = [d4Program, cnfName, "-dDNNF", "-out=" + nnfName]
    ok = runProgram("D4", root, cmd, logFile)
    if not ok and os.path.exists(nnfName):
        os.remove(nnfName)
    return ok

def runPartialGen(root, home, logFile, force):
    cnfName = home + "/" + root + ".cnf"
    nnfName = home + "/" + root + ".nnf"
    cratName = home + "/" + root + ".crat"
    cmd = [genProgram, "-p", cnfName, nnfName, cratName]
    ok = runProgram("GEN", root, cmd, logFile)
    if not ok and os.path.exists(cratName):
        os.remove(cratName)
    return ok


def runGen(root, home, logFile, force):
    extraLogName = "d2p.log"
    cnfName = home + "/" + root + ".cnf"
    nnfName = home + "/" + root + ".nnf"
    cratName = home + "/" + root + ".crat"
    if not force and os.path.exists(cratName):
        return True
    cmd = [genProgram]
    if oneSided:
        cmd += ['-1']
    if monolithic:
        cmd += ['-m']
    if not useLemma:
        cmd += ['-e']
    if not group:
        cmd += ['-s']
    cmd += ["-C", str(clauseLimit), "-L", extraLogName, cnfName, nnfName, cratName]
    ok = runProgram("GEN", root, cmd, logFile, extraLogName = extraLogName)
    checkFile("GEN", cratName, logFile)
    if not ok and os.path.exists(cratName):
        os.remove(cratName)
    return ok

def runCheck(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    cratName = home + "/" + root + ".crat"
    cmd = [checkProgram]
    if oneSided:
        cmd += ['-1']
    cmd += [cnfName, cratName]
    ok =  runProgram("FCHECK", root, cmd, logFile)
    return ok

def runLeanCheck(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    cratName = home + "/" + root + ".crat"
    cmd = [leanCheckProgram]
    cmd += [cnfName, cratName]
    ok =  runProgram("LCHECK", root, cmd, logFile)
    return ok


def runCount(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    cratName = home + "/" + root + ".crat"
    cmd = [interpreter, countProgram, "-i", cnfName, "-p", cratName]
    ok = runProgram("COUNT", root, cmd, logFile)
    return ok

def runSequence(root, home, stopD4, stopGen, stopCheck, force):
    waitWhileBlocked()
    result = ""
    prefix = "OVERALL"
    start = datetime.datetime.now()
    extension = "log"
    if oneSided:
        extension = "onesided_" + extension
    if monolithic:
        extension = "monolithic_" + extension
    if not useLemma:
        extension = "nolemma_" + extension
    if not group:
        extension = "split_" + extension
    if useLean:
        extension = "lean_" + extension
    if stopD4:
        extension = ".D4_" + extension
    if stopGen:
        extension = ".d2p_" + extension
    logName = root + "." + extension
    if not force and os.path.exists(logName):
            print("Already have file %s.  Skipping benchmark" % logName)
            return
    try:
        logFile = open(logName, 'w')
    except:
        print("%s. %s ERROR:Couldn't open file '%s'" % (root, prefix, logName))
        return
    ok = False
    done = False
    ok = runD4(root, home, logFile, force)
    if stopD4:
        ok = ok and runPartialGen(root, home, logFile, force)
        done = True
    if not done:
        ok = ok and runGen(root, home, logFile, force)
    done = done or stopGen
    if useLean:
        if not done:
            ok = ok and runLeanCheck(root, home, logFile)
        done = done or stopCheck
    else:
        if not done:
            ok = ok and runCheck(root, home, logFile)
        done = done or stopCheck
        if not done:
            ok = ok and runCount(root, home, logFile)
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
    outcome = "normal" if ok else "failed"
    result += "%s OUTCOME: %s\n" % (prefix, outcome)
    print("%s. %s OUTCOME: %s" % (root, prefix, outcome))
    print("%s. %s Elapsed time: %.3f seconds" % (root, prefix, seconds))
    logFile.write(result)
    logFile.close()

def stripSuffix(fname):
    fields = fname.split(".")
    if len(fields) > 1:
        fields = fields[:-1]
    return ".".join(fields)


def runBatch(home, fileList, stopD4, stopGen, stopCheck, force):
    roots = [stripSuffix(f) for f in fileList]
    roots = [r for r in roots if r is not None]
    print("Running on roots %s" % roots)
    for r in roots:
        runSequence(r, home, stopD4, stopGen, stopCheck, force)

def run(name, args):
    global useLemma, group, oneSided, monolithic, useLean
    home = "."
    stopD4 = False
    stopGen = False
    stopCheck = False
    force = False
    optList, args = getopt.getopt(args, "hf1mLGFs:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-f':
            force = True
        elif opt == '-1':
            oneSided = True
        elif opt == '-m':
            monolithic = True
        elif opt == '-L':
            useLemma = False
        elif opt == '-G':
            group = False
        elif opt == '-F':
            useLean = True
        elif opt == '-s':
            if val == 'n':
                stopD4 = True
            elif val == 'g':
                stopGen = True
            elif val == 'c':
                stopCheck = True
            else:
                print("Unknown stopping condition '%s'" % val)
                usage(name)
                return
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return
    runBatch(home, args, stopD4, stopGen, stopCheck, force)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    sys.exit(0)
