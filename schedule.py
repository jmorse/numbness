#!/usr/bin/python

import sys
import argparse

import config
from config import set_config, compute_bitwidths, validate_config
from z3 import Z3
from qfbv import QFBV
from qfaufbv import QFAUFBV

args = argparse.ArgumentParser(description="Produce an SMT forumla representing a schedule for teams competing in SR")

form = args.add_mutually_exclusive_group()
form.add_argument("--z3", action="store_true", default=False, dest="z3", help="Produce a formula using Z3 enumerations")
form.add_argument("--qfbv", action="store_true", default=False, dest="qfbv", help="Produce a formula with enumerated bitvector variables")
form.add_argument("--qfaufbv", action="store_true", default=False, dest="qfaufbv", help="Produce a formula using an uninterpreted function")

args.add_argument("--rounds", type=int, help="Number of rounds", default=13)
args.add_argument("--teams", type=int, help="Number of teams", default=32)
args.add_argument("--closeness", type=int, help="Closeness constraint", default=5)
args.add_argument("--slots", type=int, help="Slots per match", default=4)

the_args = args.parse_args()

set_config(the_args.rounds, the_args.teams, the_args.closeness, the_args.slots)
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

for i in range(config.NUMROUNDS):
    print "; round {0}".format(i)
    print "(assert (distinct "
    for j in range(config.NUMMATCHES):
        for k in range(config.NUMSLOTS):
            print output_object.project(i, j, k)
    print "))"

# For each round boundry,
for r in range(config.NUMROUNDS-1):
    print "; Goodness for round boundry {0}".format(r)

    # Each CLOSENESS+1 matches across the round boundry must have
    # distinct participants to ensure they always have CLOSENESS
    # matches between each match of theirs. Each CLOSENESS+1 number
    # of matches is a span, in which those matches must be distinct.
    for span in range(config.CLOSENESS):
        start_match = config.NUMMATCHES - config.CLOSENESS + span
        print "; Span goodness {0}".format(span)
        print "(assert (distinct"
        for offs in range(config.CLOSENESS + 1):
            # The range of matches we're interested in is
            # from `start_match` in the earlier round
            # through to round `span` in the later round.
            this_match = (start_match + offs) % config.NUMMATCHES
            this_round = r
            if this_match < start_match:
                this_round = r + 1

            for i in range(config.NUMSLOTS):
                print output_object.project(this_round,this_match,i)

        print "))"
    print ""

# Emit array updates representing the number of times a particular match
# pairing has occurred.
cur_array_sym = "initial_array"
for i in range(config.NUMROUNDS):
    for j in range(config.NUMMATCHES):
        # Uuuugh
        games = config.NUMSLOTS / 4
        pairings_per_game = 6
        for k in range(games):
            for l in range(pairings_per_game):
                pass


# Instruct solver to check satisfiability at this point

print "(check-sat)"

# Also, fetch the outcome from each point.

print ""
for i in range(config.NUMROUNDS):
    for j in range(config.NUMMATCHES):
        for k in range(config.NUMSLOTS):
            pass
            print "(get-value ({0}))".format(output_object.project(i, j, k))
