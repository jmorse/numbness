#!/usr/bin/python

import sys

# More flexible parameters
NUMROUNDS = 2
NUMMATCHES = 3
NUMTEAMS = 12

close_constraints = True
CLOSENESS = 2

# More built in parameters.
NUMSLOTS = 4

# Underlying bitwidths
ROUNDBITS = 4
MATCHBITS = 4
SLOTBITS = 2
TEAMBITS = 6

# Optionally use more more elaborate Z3 things
USE_Z3 = False

# Integer constants are different in different logics
def print_integer(val, width):
	return "(_ bv{0} {1})".format(val, width)

def sparticus(r, match, slot):
	return "(sparticus {0} {1} {2})".format(print_integer(r, ROUNDBITS),
			print_integer(match, MATCHBITS),
			print_integer(slot, SLOTBITS))

print "(set-info :status unknown)"
print "(set-option :produce-models true)"
if USE_Z3:
	print "; Logic is now \"Whatever Z3 accepts\" (set-logic AUFBV)"
else:
	print "(set-logic QF_AUFBV)"
print ""

# Configurable number of enum members

if USE_Z3:
	print "(declare-datatypes () ((TEAM "
	for i in range(NUMTEAMS):
		print "t{0}".format(i),
	print ")))"

	# The uninterpreted function that's going to become our scheduler.
	# Takes a 4 bit round, 4 bit match, 2 bit slot, returns a team.
	print ""
	print "(declare-fun sparticus ((_ BitVec {0}) (_ BitVec {1}) (_ BitVec {2})) TEAM)".format(ROUNDBITS, MATCHBITS, SLOTBITS)
	print ""
else:
	print ""
	print "(declare-fun sparticus ((_ BitVec {0}) (_ BitVec {1}) (_ BitVec {2})) (_ BitVec {3}))".format(ROUNDBITS, MATCHBITS, SLOTBITS, TEAMBITS)
	print ""

	# If not Z3, don't use enum type, and instead we have some bitvectors
	# with one number identifying one team. Constraint to the number of
	#teams.
	for i in range(NUMROUNDS):
		for j in range(NUMMATCHES):
			for k in range(NUMSLOTS):
				print "(assert (bvult ",
				print sparticus(i, j, k),
				print print_integer(NUMTEAMS, TEAMBITS),
				print "))"

# Ensure all slots over all matchs per round are distinct.

for i in range(NUMROUNDS):
	print "; round {0}".format(i)
	print "(assert (distinct "
	for j in range(NUMMATCHES):
		for k in range(NUMSLOTS):
			print sparticus(i, j, k)
	print "))"

# Optionally add goodness constraints.
if close_constraints:
	if CLOSENESS >= NUMMATCHES:
		print >>sys.stderr, "Match close constraints allows no matches"
		sys.exit(1)

	# For each round boundry,
	for r in range(NUMROUNDS-1):
		print "; Goodness for round boundry {0}".format(r)
		print "(assert (distinct"

		# Each CLOSENESS+1 matches across the round boundry must have
		# distinct participants to ensure they always have CLOSENESS
		# matches between each match of theirs. Each CLOSENESS+1 number
		# of matches is a span, in which those matches must be distinct.
		for span in range(CLOSENESS + 1):
			start_match = NUMMATCHES - CLOSENESS + span
			for offs in range(CLOSENESS + 1):
				# The range of matches we're interested in is
				# from `start_match` in the earlier round
				# through to round `span` in the later round.
				this_match = (start_match + offs) % NUMMATCHES
				this_round = r
				if this_match < start_match:
					this_round = r + 1

				for i in range(NUMSLOTS):
					print sparticus(this_round,this_match,i)

		print "))"
		print ""

print "(check-sat)"

# Also, fetch the outcome from each point.

print ""
for i in range(NUMROUNDS):
	for j in range(NUMMATCHES):
		for k in range(NUMSLOTS):
			pass
			print "(get-value ((sparticus {0} {1} {2})))".format(
					print_integer(i, ROUNDBITS),
					print_integer(j, MATCHBITS),
					print_integer(k, SLOTBITS))
