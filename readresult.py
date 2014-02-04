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

hashchar = Literal('#')
bchar = Literal('b')
lparen = Literal('(')
rparen = Literal(')')
symbol = Word(alphas + "_" + "0123456789") # Not the whole smtlib range, but meh
bit = Word("01")
bitvec  = Group(hashchar + bchar + OneOrMore(bit))

# Our expr:
expr = Forward()
expr << Group((lparen + symbol + expr + rparen) | (lparen + symbol + expr + expr + rparen) | (lparen + symbol + expr + expr + expr + rparen) | symbol | bitvec)

# Pairs of results for the output.
outpair = Group(lparen + lparen + expr + expr + rparen + rparen)
everything = OneOrMore(outpair)

# Read /all the things/

foo = everything.parseFile(sys.stdin)
print repr(foo)
for assignment in foo:
	paren1, paren2, expr1, expr2, paren3, paren4 = assignment
	# expr1 is the source name, expr2 the actual value.
	# Do some things
