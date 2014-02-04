#!/usr/bin/python

import sys

from config import *
from z3 import Z3
from qfbv import QFBV
from qfaufbv import QFAUFBV

# Optionally use more more elaborate Z3 things
USE_Z3 = False

print "(set-info :status unknown)"
print "(set-option :produce-models true)"

output_object = None
if USE_Z3:
	output_object = Z3()
else:
	output_object = QFAUFBV()

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

# Optionally add goodness constraints.
if close_constraints:
	if CLOSENESS >= NUMMATCHES:
		print >>sys.stderr, "Match close constraints allows no matches"
		sys.exit(1)

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
