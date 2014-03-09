#!/usr/bin/python

import sys
import argparse

from config import *
from z3 import Z3
from qfbv import QFBV
from qfaufbv import QFAUFBV

args = argparse.ArgumentParser(description="Produce an SMT forumla representing a schedule for teams competing in SR")

form = args.add_mutually_exclusive_group()
form.add_argument("--z3", action="store_true", default=False, dest="z3", help="Produce a formula using Z3 enumerations")
form.add_argument("--qfbv", action="store_true", default=False, dest="qfbv", help="Produce a formula with enumerated bitvector variables")
form.add_argument("--qfaufbv", action="store_true", default=False, dest="qfaufbv", help="Produce a formula using an uninterpreted function")

args.add_argument("--rounds", type=int, help="Number of rounds", default=0)
args.add_argument("--teams", type=int, help="Number of teams", default=0)
args.add_argument("--closeness", type=int, help="Closeness constraint", default=0)

the_args = args.parse_args()

if the_args.rounds != 0:
    NUMROUNDS = the_args.rounds
if the_args.teams != 0:
    NUMTEAMS = the_args.teams
if the_args.closeness != 0:
    CLOSENESS = the_args.closeness

compute_bitwidths()
validate_config()

print "(set-info :status unknown)"
print "(set-option :produce-models true)"

output_object = None
if the_args.z3:
	output_object = Z3()
elif the_args.qfaufbv:
	output_object = QFAUFBV()
elif the_args.qfbv:
	output_object = QFBV()
else:
	output_object = QFBV()

output_object.preamble()

# Ensure all slots over all matchs per round are distinct.

for i in range(NUMROUNDS):
	print "; round {0}".format(i)
	print "(assert (distinct "
	for j in range(NUMMATCHES):
		for k in range(NUMSLOTS):
			print output_object.project(i, j, k)
	print "))"

# For each round boundry,
for r in range(NUMROUNDS-1):
    print "; Goodness for round boundry {0}".format(r)

    # Each CLOSENESS+1 matches across the round boundry must have
    # distinct participants to ensure they always have CLOSENESS
    # matches between each match of theirs. Each CLOSENESS+1 number
    # of matches is a span, in which those matches must be distinct.
    for span in range(CLOSENESS):
        start_match = NUMMATCHES - CLOSENESS + span
        print "; Span goodness {0}".format(span)
        print "(assert (distinct"
        for offs in range(CLOSENESS + 1):
            # The range of matches we're interested in is
            # from `start_match` in the earlier round
            # through to round `span` in the later round.
            this_match = (start_match + offs) % NUMMATCHES
            this_round = r
            if this_match < start_match:
                this_round = r + 1

            for i in range(NUMSLOTS):
                print output_object.project(this_round,this_match,i)

        print "))"
    print ""

# Instruct solver to check satisfiability at this point

print "(check-sat)"

# Also, fetch the outcome from each point.

print ""
for i in range(NUMROUNDS):
	for j in range(NUMMATCHES):
		for k in range(NUMSLOTS):
			pass
			print "(get-value ({0}))".format(output_object.project(i, j, k))
