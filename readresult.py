#!/usr/bin/python

import sys

# This expects to read one line containing the status ("sat"), then a bunch of
# lisp expressions produced by the get-value queries at the end of the script.

line = sys.stdin.readline()
line = line[0:-1] # chop newline

if line == "unsat":
	print "You've won a prize: the formula is unsatisfiable!"
	sys.exit(1)
else if line != "sat":
	print "Unrecognized get-sat result: {0}".format(line)
	sys.exit(1)
