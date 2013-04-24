#!/usr/bin/python

print "(set-info :status unknown)"
print "(set-option :produce-models true)"
print "; Logic is now \"Whatever Z3 accepts\" (set-logic AUFBV)"
print ""

# Configurable number of enum members

print "(declare-datatypes () ((TEAM "
for i in range(12):
	print "t{0}".format(i),

print ")"

# The uninterpreted function that's going to become our scheduler. Takes a
# 4 bit round, 4 bit match, 2 bit slot, returns a team.
print ""
print "(declare-fun sparticus ((_ BitVec 4) (_ BitVec 4) (_ BitVec 2)) TEAM)"
print ""
