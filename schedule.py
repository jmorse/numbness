#!/usr/bin/python

# More flexible parameters
NUMROUNDS = 2
NUMMATCHES = 3

# More built in parameters.
NUMTEAMS = 12
ROUNDBITS = 4
MATCHBITS = 4
SLOTBITS = 2

print "(set-info :status unknown)"
print "(set-option :produce-models true)"
print "; Logic is now \"Whatever Z3 accepts\" (set-logic AUFBV)"
print ""

# Configurable number of enum members

print "(declare-datatypes () ((TEAM "
for i in range(NUMTEAMS):
	print "t{0}".format(i),

print ")"

# The uninterpreted function that's going to become our scheduler. Takes a
# 4 bit round, 4 bit match, 2 bit slot, returns a team.
print ""
print "(declare-fun sparticus ((_ BitVec {0}) (_ BitVec {1}) (_ BitVec {2})) TEAM)".format(ROUNDBITS, MATCHBITS, SLOTBITS)
print ""

# Ensure all slots over all matchs per round are distinct.

for i in range(NUMROUNDS):
	for j in range(NUMMATCHES):
		pass
