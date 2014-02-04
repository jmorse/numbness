#!/usr/bin/python

import sys

from pyparsing import nums, oneOf, Word, Literal, Suppress, alphas
from pyparsing import ParseException, Forward, Group, OneOrMore

# This expects to read one line containing the status ("sat"), then a bunch of
# lisp expressions produced by the get-value queries at the end of the script.

line = sys.stdin.readline()
line = line[0:-1] # chop newline

if line == "unsat":
	print "You've won a prize: the formula is unsatisfiable!"
	sys.exit(1)
elif line != "sat":
	print "Unrecognized get-sat result: {0}".format(line)
	sys.exit(1)

# Build a pyparsing thing.

newline = Literal('\n')
lparen = Literal('(')
rparen = Literal(')')
symbol = Word(alphas + "_" + "0123456789") # Not the whole smtlib range, but meh

# Our expr:
expr = Forward()
expr << Group(lparen + symbol + expr + rparen)
expr << Group(lparen + symbol + expr + expr + rparen)
expr << Group(lparen + symbol + expr + expr + expr + rparen)
expr << symbol

# Pairs of results for the output.
outpair = Group(lparen + lparen + expr + expr + rparen + rparen + newline)
everything = OneOrMore(outpair)

# Read /all the things/

inputblob = sys.stdin.read(1000000)
foo = everything.parseString(inputblob)
print repr(foo)
