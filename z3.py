from config import *
from util import *

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

	def read_variable(self, expr):
		return read_func_var(expr)

	pass

