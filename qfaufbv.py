from config import *
from util import *

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

