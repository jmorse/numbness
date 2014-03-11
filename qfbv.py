import config
import re
from util import *

class QFBV:
    def preamble(self):
        print "(set-logic QF_BV)"

        print ""

        # Enumerate all the variables, for each match round.
        for i in range(config.NUMROUNDS):
            for j in range(config.NUMMATCHES):
                for k in range(config.NUMSLOTS):
                    print "(declare-fun {0} () (_ BitVec {1}))".format(self.project(i, j, k), config.TEAMBITS)

        # Do we need to add additional assertions...
        if pow(2, config.TEAMBITS) == config.NUMTEAMS:
            return

        # And assert that they're in range
        for i in range(config.NUMROUNDS):
            for j in range(config.NUMMATCHES):
                for k in range(config.NUMSLOTS):
                    print "(assert (bvult {0} {1}))".format(self.project(i, j, k), print_integer(config.NUMTEAMS, config.TEAMBITS))

        print "(declare-fun faced_array () (Array (_ BitVec {0}) (_ BitVec {0})))".format(config.TEAMBITS*2, config.MATCHBITS)

    def project(self, x, y, z):
        return "round_{0}_match_{1}_slot_{2}".format(x, y, z)

    pass

    def read_variable(self, expr1):
        string, = expr1
        regex = "round_([0-9]+)_match_([0-9]+)_slot_([0-9]+)"
        result = re.match(regex, string)
        return int(result.group(1)), int(result.group(2)), int(result.group(3))
