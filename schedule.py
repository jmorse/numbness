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
