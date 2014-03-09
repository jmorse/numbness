import config
from util import *

class QFAUFBV:
	def preamble(self):
		print "(set-logic QF_AUFBV)"

		print ""
		print "(declare-fun sparticus ((_ BitVec {0}) (_ BitVec {1}) (_ BitVec {2})) (_ BitVec {3}))".format(config.ROUNDBITS, config.MATCHBITS, config.SLOTBITS, config.TEAMBITS)
		print ""

		# If not Z3, don't use enum type, and instead we have some
		# bitvectors with one number identifying one team. Constraint
		# to the number of teams.
		for i in range(config.NUMROUNDS):
			for j in range(config.NUMMATCHES):
				for k in range(config.NUMSLOTS):
					print "(assert (bvult ",
					print self.project(i, j, k),
					print print_integer(config.NUMTEAMS, config.TEAMBITS),
					print "))"

	def project(self, x, y, z):
		return sparticus(x, y, z)

	def read_variable(self, expr):
		return read_func_app(expr)

	pass

