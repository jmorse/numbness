from config import *
import re

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

	def read_variable(self, expr1):
		string, = expr1
		regex = "round_([0-9]+)_match_([0-9]+)_slot_([0-9]+)"
		result = re.match(regex, string)
		return int(result.group(1)), int(result.group(2)), int(result.group(3))
