#!/usr/bin/python3

#####################################################################################
# Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University
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


# Model counter for CPOG files
import sys
import getopt
import datetime

        
# Undocumented way to enable printing of very large numbers
try:
    sys.set_int_max_str_digits(0)
except:
    pass

def usage(name):
    print("Usage: %s -i FILE.cnf -p FILE.cpog [-w W1:W2:...:Wn]" % name)
    print("   -w WEIGHTS   Provide colon-separated set of input weights.")
    print("                Each should be between 0 and 100 (will be scaled by 1/100)")


######################################################################################
# Design options
######################################################################################


######################################################################################
# CPOG Syntax
######################################################################################
# Notation
#  Id: Clause Id
#  Var: Variable
#  Lit: Literal +/- Var

# Lit*: Clause consisting of specified literals
# HINT: Either Id+ or *

#     r lit                  -- Declare root literal
# Id  a [Lit*] 0    HINT 0   -- RUP clause addition
#     d Id          HINT 0   -- RUP clause deletion
# Id  p Var Lit*         0   -- And operation
# Id  a Var Lit Lit HINT 0   -- Or operation

######################################################################################

def trim(s):
    while len(s) > 0 and s[-1] in ' \r\n\t':
        s = s[:-1]
    return s


class CountException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "COUNTER Exception: " + str(self.value)

class PNumException(Exception):
    msg = ""

    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return "P52 Number exception %s" % self.msg



# Represent numbers of form a * 2**m2 + 5**m5
class P52:
    a = 1
    m2 = 0
    m5 = 0

    def __init__(self, a=0, m2=0, m5=0):
        if type(a) != type(1):
            raise PNumException("Nonintegral a (%s)" % str(a))
        if type(m2) != type(1):
            raise PNumException("Nonintegral m2 (%s)" % str(m2))
        if type(m5) != type(1):
            raise PNumException("Nonintegral m5 (%s)" % str(m5))
        if a == 0:
            self.a = a
            self.m2 = 0
            self.m5 = 0
            return
        while a % 2 == 0:
            a = a//2
            m2 += 1
        while a % 5 == 0:
            a = a//5
            m5 += 1
        self.a = a
        self.m2 = m2
        self.m5 = m5

    def __str__(self):
        return "%d*2^(%d)5^(%d)" % (self.a, self.m2, self.m5)

    def __eq__(self, other):
        return self.a == other.a and self.m2 == other.m2 and self.m5 == other.m5

    def num(self):
        p2 = 2**self.m2
        p5 = 5**self.m5
        val = self.a * p2 * p5
        return val

    def neg(self):
        result = P52(-self.a, self.m2, self.m5)
        return result

    def oneminus(self):
        one = P52(1)
        result = one.add(self.neg())
        return result

    def mul(self, other):
        na = self.a * other.a 
        nm2 = self.m2 + other.m2
        nm5 = self.m5 + other.m5
        result =  P52(na, nm2, nm5)
        return result

    # This only works for case where a == 1
    def recip(self):
        if self.a != 1:
            return None
        return P52(self.a, -self.m2, -self.m5)

    def add(self, other):
        ax = self.a
        ay = other.a
        m2x = self.m2
        m2y = other.m2
        m5x = self.m5
        m5y = other.m5
        if m2y > m2x:
            d2 = m2y-m2x
            ay *= 2**d2
            m2n = m2x
        else:
            d2 = m2x-m2y
            ax *= 2**d2
            m2n = m2y
        if m5y > m5x:
            d5 = m5y-m5x
            ay *= 5**d5
            m5n = m5x
        else:
            d5 = m5x-m5y
            ax *= 5**d5
            m5n = m5y
        an = ax+ay
        result = P52(an, m2n, m5n)
        return result

    def scale2(self, x):
        return P52(self.a, self.m2+x, self.m5)
    def scale5(self, x):
        return P52(self.a, self.m2, self.m5+x)
    def scale10(self, x):
        return P52(self.a, self.m2+x, self.m5+x)

    def parse(self, s):
        if len(s) == 0:
            raise PNumException("Invalid number '%s'" % s)
        negative = s[0] == '-'
        if negative:
            s = s[1:]
        fields = s.split('e')
        p10 = 0
        if len(fields) == 2:
            try:
                p10 = int(fields[1])
                s = fields[0]
            except:
                raise PNumException("Invalid number '%s'" % s)
        fields = s.split('.')
        if len(fields) == 1:
            try:
                ival = int(fields[0])
                if negative:
                    ival = -ival
            except:
                raise PNumException("Invalid number '%s'" % s)
            val = P52(ival)
            if p10 != 0:
                val = val.scale10(p10)
            return val
        elif len(fields) == 2:
            try:
                h = int(fields[0]) if len(fields[0]) > 0 else 0
                l = int(fields[1]) if len(fields[1]) > 0 else 0
                if negative:
                    h = -h
                    l = -l
            except:
                raise PNumException("Invalid number '%s'" % s)
            wt = len(fields[1])
            val = P52(h).add(P52(l,-wt,-wt))
            if p10 != 0:
                val = val.scale10(p10)
            return val
        else:
            raise PNumException("Invalid number '%s'" % s)

    def render(self):
        if self.a < 0:
            sign = "-"
            ival = -self.a
        else:
            sign = ""
            ival = self.a
        p10 = min(self.m2, self.m5)
        if self.m2 > p10:
            ival *= 2**(self.m2 - p10)
        elif self.m5 > p10:
            ival *= 5**(self.m5 - p10)
        sval = str(ival)
        if p10 >= 0:
            sval += '0' * p10
        elif -p10 >= len(sval):
            sval = '0.' + '0' * -(p10+len(sval)) + sval
        else:
            pos = len(sval) + p10
            sval = sval[:pos] + '.' + sval[pos:]
        return sign+sval

# Read CNF file.
# Extract number of variables and any weight information
class CnfReader():
    file = None
    weights = None
    finalScale = None
    # List of input variables.
    nvar = 0
    failed = False
    errorMessage = ""
    
    def __init__(self, fname):
        self.failed = False
        self.errorMessage = ""
        self.weights = None
        try:
            self.file = open(fname, 'r')
        except Exception:
            self.fail("Could not open file '%s'" % fname)
            return
        self.readCnf()
        self.file.close()
        
    def fail(self, msg):
        self.failed = True
        self.errorMessage = msg

    # See if there's anything interesting in the comment
    def processComment(self, line):
        if self.weights is None:
            if self.nvar > 0:
                # Already past point where weight header will show up
                return
            fields = line.split()
            if len(fields) == 3 and fields[1] == 't' and fields[2] == 'wmc':
                self.weights = {}
        else:
            fields = line.split()
            if len(fields) == 6 and fields[1] == 'p' and fields[2] == 'weight':
                lit = int(fields[3])
                wt = P52().parse(fields[4])
                if lit > 0:
                    self.weights[lit] = wt
                elif -lit in self.weights:
                    pwt = self.weights[-lit]
                    swt = wt.add(pwt)
                    if swt != P52(1):
                        # Try to normalize
                        rwt = swt.recip()
                        if rwt is None:
                            msg = "Cannot normalize weights: w(%d) = %s, w(%d) = %s" % (-lit, pwt.render(), lit, wt.render())
                            self.fail(msg)
                            return
                        self.weights[-lit] = self.weights[-lit].mul(rwt)
                        if self.finalScale is None:
                            self.finalScale = swt
                        else:
                            self.finalScale = self.finalScale.mul(swt)


    def readCnf(self):
        self.nvar = 0
        lineNumber = 0
        nclause = 0
        clauseCount = 0
        for line in self.file:
            lineNumber += 1
            line = trim(line)
            if len(line) == 0:
                continue
            elif line[0] == 'c':
                self.processComment(line)
            elif line[0] == 'p':
                fields = line[1:].split()
                if fields[0] != 'cnf':
                    self.fail("Line %d.  Bad header line '%s'.  Not cnf" % (lineNumber, line))
                    return
                try:
                    self.nvar = int(fields[1])
                    nclause = int(fields[2])
                except Exception:
                    self.fail("Line %d.  Bad header line '%s'.  Invalid number of variables or clauses" % (lineNumber, line))
                    return
            else:
                continue


class OperationManager:
    conjunction, disjunction = range(2)
    
    # Number of input variables
    inputVariableCount = 0
    # Operation indexed by output variable.  Each entry of form (id, op, arg1, arg2, ...)
    operationDict = {}

    def __init__(self, varCount):
        self.inputVariableCount = varCount
        self.operationDict = {}

    def addOperation(self, op, outVar, inLits, id):
        if op == self.disjunction:
            if len(inLits) != 2:
                return (False, "Cannot have %d arguments for disjunction" % len(inLits))
# REVISED
#        elif op == self.conjunction:
#            if len(inLits) < 2:
#                return (False, "Cannot have %d arguments for conjunction" % len(inLits))
        self.operationDict[outVar] = tuple([op] + inLits)
        return (True, "")

    def haveOperation(self, outVar):
        return outVar in self.operationDict

    def deleteOperation(self, outVar):
        return (True, "")

    def pnumCount(self, root, weights, finalScale = None):
        for outVar in sorted(self.operationDict.keys()):
            entry = self.operationDict[outVar]
            op = entry[0]
            args = entry[1:]
            wts = []
            for arg in args:
                var = abs(arg)
                val = weights[var]
                if arg < 0:
                    val = val.oneminus()
                wts.append(val)
            result = wts[0]
            for w in wts[1:]:
                result = result.mul(w) if op == self.conjunction else result.add(w)
            weights[outVar] = result
        rootVar = abs(root)
        rval = weights[rootVar]
        if root < 0:
            rval = rval.oneminus()
        if finalScale is not None:
            rval = rval.mul(finalScale)
        return rval
    

    # Optionally provide dictionary of weights.  Otherwise assume unweighted
    def count(self, root, weights = None, finalScale = None):
        if weights is None:
            weights = { v : P52(1,-1,0) for v in range(1, self.inputVariableCount+1) }
            finalScale = P52(1, self.inputVariableCount, 0)
        pval = self.pnumCount(root, weights, finalScale)
        return pval

class Builder:
    verbose = False
    lineNumber = 0
    # Operation Manager
    omgr = None
    rootLiteral = None
    failed = False

    def __init__(self, creader):
        self.lineNumber = 0
        self.omgr = OperationManager(creader.nvar)
        self.failed = False
        self.lineNumber = 0
        self.rootLiteral = None

    def flagError(self, msg):
        print("COUNTER: ERROR.  Line %d: %s" % (self.lineNumber, msg))
        self.failed = True

    # Find zero-terminated list of integers in fields (or single field consisting of '*').  Return (list, rest)
    # Flag error if something goes wrong
    def findList(self, fields, starOk = False):
        ls = []
        rest = fields
        starOk = True
        while len(rest) > 0:
            field = rest[0]
            rest = rest[1:]
            if starOk and field == '*':
                val = '*'
            else:
                try:
                    val = int(field)
                except:
                    self.flagError("Non-integer value '%s' encountered" % field)
                    return (ls, rest)
            if val == 0:
                return (ls, rest)
            ls.append(val)
            starOk = False
        self.flagError("No terminating 0 found")
        return (ls, rest)

    def build(self, fname):
        if self.failed:
            self.failBuild("Problem with CNF file")
            return
        try:
            pfile = open(fname)
        except:
            self.failBuild("Couldn't open proof file '%s" % fname)
            return
        for line in pfile:
            self.lineNumber += 1
            fields = line.split()
            if len(fields) == 0 or fields[0][0] == 'c':
                continue
            id = None
            if fields[0] not in ['dc', 'do', 'r']:
                try:
                    id = int(fields[0])
                except:
                    self.flagError("Looking for clause Id.  Got '%s'" % fields[0])
                    break
                fields = fields[1:]
            cmd = fields[0]
            rest = fields[1:]
            # Dispatch on command
            # Level command requires special consideration, since it only occurs at beginning of file
            if cmd == 'i':
                pass
            elif cmd == 'a':
                self.doAddRup(id, rest)
            elif cmd == 'dc':
                pass
            elif cmd == 'r':
                self.doDeclareRoot(id, rest)
            elif cmd == 'p':
                self.doProduct(id, rest)
            elif cmd == 's':
                self.doSum(id, rest)
            elif cmd == 'do':
                pass
            else:
                self.invalidCommand(cmd)
            if self.failed:
                break
            if self.rootLiteral is not None and self.omgr.haveOperation(self.rootLiteral):
                break
        pfile.close()
            
    def count(self, weights = None, finalScale = None):
        if self.rootLiteral is None:
            print("COUNTER: Can't determine count.  Don't know root")
            return P52()
        return self.omgr.count(self.rootLiteral, weights, finalScale)

    def invalidCommand(self, cmd):
        self.flagError("Invalid command '%s' in proof" % cmd)

    def doAddRup(self, id, rest):
        (lits, rest) = self.findList(rest)
        if self.failed:
            return
        if len(lits) == 1 and self.rootLiteral is None:
            self.rootLiteral = lits[0]
        
    def doDeclareRoot(self, id, rest):
        if len(rest) != 1:
            self.flagError("Root declaration should consist just of root literal")
            return
        try:
            rlit = int(rest[0])
        except:
            self.flagError("Invalid root literal '%s'", rest[0])
            return
        self.rootLiteral = rlit


    def doProduct(self, id, rest):
# REVISED
#        if len(rest) < 2:
#            self.flagError("Couldn't add product operation with clause #%d: Invalid number of operands" % (id))
#            return
        try:
            args = [int(field) for field in rest]
        except:
            self.flagError("Couldn't add operation with clause #%d: Non-integer arguments" % (id))
            return
        if args[-1] != 0:
            self.flagError("Couldn't add operation with clause #%d: No terminating 0 found" % (id))
            return
        args = args[:-1]
        (ok, msg) = self.omgr.addOperation(self.omgr.conjunction, args[0], args[1:], id)
        if not ok:
            self.flagError("Couldn't add operation with clause #%d: %s" % (id, msg))

    def doSum(self, id, rest):
        if len(rest) < 3:
            self.flagError("Couldn't add sum operation with clause #%d: Invalid number of operands" % (id))
            return
        try:
            args = [int(field) for field in rest[:3]]
            rest = rest[3:]
        except:
            self.flagError("Couldn't add operation with clause #%d: Non-integer arguments" % (id))
            return
        (ok, msg) = self.omgr.addOperation(self.omgr.disjunction, args[0], [args[1], args[2]], id)
        if not ok:
            self.flagError("Couldn't add operation with clause #%d: %s" % (id, msg))
            return

    def failBuild(self, reason):
        self.failed = True
        msg = "CONSTRUCTION OF POG FAILED"
        if reason != "":
            msg += ": " + reason
        print(msg)

def run(name, args):
    cnfName = None
    proofName = None
    weights = None
    finalScale = None
    optList, args = getopt.getopt(args, "hi:p:w:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return True
        elif opt == '-i':
            cnfName = val
        elif opt == '-p':
            proofName = val
        elif opt == '-w':
            wlist = val.split(":")
            try:
                weights = { v : P52(int(wlist[v-1]), -2, -2) for v in range(1, len(wlist)+1) }
            except Exception as ex:
                print("COUNTER: Couldn't extract weights from '%s' (%s)" % (val, str(ex)))
                usage(name)
                return False
        else:
            usage(name)
            return False
    if cnfName is None:
        print("COUNTER: Need CNF file name")
        return False
    if proofName is None:
        print("COUNTER: Need CPOG file name")
        return False
    start = datetime.datetime.now()
    creader = CnfReader(cnfName)
    if creader.failed:
        print("Error reading CNF file: %s" % creader.errorMessage)
        print("PROOF FAILED")
        return False
    if weights is None:
        if creader.weights is not None:
            print("Obtained weights from CNF file")
            weights = creader.weights
            finalScale = creader.finalScale
    if weights is not None and len(weights) != creader.nvar:
        print("Invalid set of weights.  Should provide %d.  Got %d" % (creader.nvar, len(weights)))
        return False
    builder = Builder(creader)
    builder.build(proofName)
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    count = builder.count(weights, finalScale)
    print("COUNTER: Elapsed time for count: %.2f seconds" % seconds)
    if weights is None:
        print("COUNTER: Unweighted count = %s" % count.render())
    else:
        print("COUNTER: Weighted count = %s" % count.render())
    return True
    
if __name__ == "__main__":
    ok = run(sys.argv[0], sys.argv[1:])
    if ok:
        sys.exit(0)
    else:
        sys.exit(1)
    
