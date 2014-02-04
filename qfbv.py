from config import *

class QFBV:
	def preamble(self):
		print "(set-logic QF_BV)"

		print ""

		# Enumerate all the variables, for each match round.
		for i in range(NUMROUNDS):
			for j in range(NUMMATCHES):
				for k in range(NUMSLOTS):
					print "(declare-fun {0} () (_ BitVec {1}))".format(self.project(i, j, k), TEAMBITS)

	def project(self, x, y, z):
		return "round_{0}_match_{1}_slot_{2}".format(x, y, z)

	pass

