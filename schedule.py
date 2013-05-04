#!/usr/bin/python

import sys

# More flexible parameters
NUMROUNDS = 13
NUMMATCHES = 8
NUMTEAMS = 32

close_constraints = True
CLOSENESS = 5

min_met_constraints = True
MINMET = 1
METBITS = 4

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
					print sparticus(this_round,this_match,i)

			print "))"
		print ""


if min_met_constraints:
	# Optionally state that, as a bare minimum, each team must meet
	# at least N other teams. State this as being some other uninterpreted
	# functions that for 0..MINMET as inputs return the round/match/slots
	# identifying pairings of matches containing this team and a distinct
	# other team.
	print "; Func declarations for min-met constraints"
	print "(declare-fun pick_met_match_round ((_ BitVec {0}) (_ BitVec {1})) (_ BitVec {2}))".format(TEAMBITS, METBITS, ROUNDBITS)
	print "(declare-fun pick_met_match_match ((_ BitVec {0}) (_ BitVec {1})) (_ BitVec {2}))".format(TEAMBITS, METBITS, MATCHBITS)
	print "(declare-fun pick_met_match_slot ((_ BitVec {0}) (_ BitVec {1}) Bool) (_ BitVec {2}))".format(TEAMBITS, METBITS, SLOTBITS)

	# Enumerate the pairings for each team.
	for i in range(NUMTEAMS):
		this_team_str = print_integer(i, TEAMBITS)
		print "; min-met constraints for team {0}".format(i)
		# The encoding: that calling sparticus with the outputs of the
		# above functions, with the thisteam argument as true, always
		# returns this team ID; and doing the same with thisteam set to
		# false identifies a bunch of other teams.

		# First, the constraint that we're picking matches with this
		# team in it.
		# Up to MINMET pairings,
		for j in range(MINMET):
			this_met_idx = print_integer(j, METBITS)
			print "(assert (= {0}".format(this_team_str),
			print "(sparticus {0} {1} {2})))".format(
				"(pick_met_match_round {0} {1})"
				.format(this_team_str, this_met_idx),
				"(pick_met_match_match {0} {1})"
				.format(this_team_str, this_met_idx),
				"(pick_met_match_slot {0} {1} true)"
				.format(this_team_str, this_met_idx))

			# Also constrain that the round/match/slot picked must
			# be in range
			print "(assert (bvule (pick_met_match_round {0} {1}) {2}))".format(this_team_str, this_met_idx, print_integer(NUMROUNDS, ROUNDBITS))
			print "(assert (bvule (pick_met_match_match {0} {1}) {2}))".format(this_team_str, this_met_idx, print_integer(NUMMATCHES, MATCHBITS))
			# FIXME: don't assert anything about slots, only valid
			# ones are in the domain of (_ BitVec 2)
			#print "(assert (bvule (pick_met_match_slot {0} {1}) {2}))".format(this_team_str, this_met_idx, print_integer(NUMSLOTS, SLOTBITS))

		# Now constraint that all the other matches are distinct. Plus
		# distinct from the team we're working on now, just in case the
		# solver sneakily slips them in there.
		print "; Distinct-min-met outputs for team {0}".format(i)
		print "(assert (distinct {0}".format(this_team_str)
		for j in range(MINMET):
			this_met_idx = print_integer(j, METBITS)
			print "(sparticus {0} {1} {2})".format(
				"(pick_met_match_round {0} {1})"
				.format(this_team_str, this_met_idx),
				"(pick_met_match_match {0} {1})"
				.format(this_team_str, this_met_idx),
				"(pick_met_match_slot {0} {1} false)"
				.format(this_team_str, this_met_idx))
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
			print "(get-value ((sparticus {0} {1} {2})))".format(
					print_integer(i, ROUNDBITS),
					print_integer(j, MATCHBITS),
					print_integer(k, SLOTBITS))
