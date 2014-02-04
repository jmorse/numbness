#!/usr/bin/python

import sys

# More flexible parameters
NUMROUNDS = 13
NUMMATCHES = 8
NUMTEAMS = 32

close_constraints = True
CLOSENESS = 5

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

class Z3:
	def preamble(self):
		print "; Logic is now \"Whatever Z3 accepts\" (set-logic AUFBV)"

		print "(declare-datatypes () ((TEAM "
		for i in range(NUMTEAMS):
			print "t{0}".format(i),
		print ")))"

		# The uninterpreted function that's going to become our
		# scheduler. Takes a 4 bit round, 4 bit match, 2 bit slot,
		# returns a team.
		print ""
		print "(declare-fun sparticus ((_ BitVec {0}) (_ BitVec {1}) (_ BitVec {2})) TEAM)".format(ROUNDBITS, MATCHBITS, SLOTBITS)
		print ""

	def project(self, x, y, z):
		return sparticus(x, y, z)

	pass

class QFAUFBV:
	def preamble(self):
		print "(set-logic QF_AUFBV)"

		print ""
		print "(declare-fun sparticus ((_ BitVec {0}) (_ BitVec {1}) (_ BitVec {2})) (_ BitVec {3}))".format(ROUNDBITS, MATCHBITS, SLOTBITS, TEAMBITS)
		print ""

		# If not Z3, don't use enum type, and instead we have some
		# bitvectors with one number identifying one team. Constraint
		# to the number of teams.
		for i in range(NUMROUNDS):
			for j in range(NUMMATCHES):
				for k in range(NUMSLOTS):
					print "(assert (bvult ",
					print self.project(i, j, k),
					print print_integer(NUMTEAMS, TEAMBITS),
					print "))"

	def project(self, x, y, z):
		return sparticus(x, y, z)

	pass

output_object = None
if USE_Z3:
	output_object = Z3()
else:
	output_object = QFAUFBV()

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
