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

        array_domain_w = config.TEAMBITS*2

        print "(declare-fun initial_free_array () (Array (_ BitVec {0}) (_ BitVec {1})))".format(config.TEAMBITS*2, config.MATCHBITS)

        print "(declare-fun initial_array () (Array (_ BitVec {0}) (_ BitVec {1})))".format(config.TEAMBITS*2, config.MATCHBITS)

        # Alas, we have to zero-initialize the initial array.
        print "(assert (= initial_array "
        for i in range(config.NUMTEAMS):
            for j in range(config.NUMTEAMS):
                print "(store "

        print "initial_free_array "

        for i in range(config.NUMTEAMS):
            for j in range(config.NUMTEAMS):
                print "(_ bv{0} {1}) (_ bv0 {2}) )".format(((i << config.TEAMBITS) + j), array_domain_w, config.MATCHBITS)

        print "))"


        for i in range(config.NUMROUNDS):
            for j in range(config.NUMMATCHES):
                # Uuuugh
                games = config.NUMSLOTS / 4
                pairings_per_game = 6
                for k in range(games):
                    for l in range(pairings_per_game):
                        print "(declare-fun faced_array_r{0}_m{1}_g{2}_p{3} () (Array (_ BitVec {4}) (_ BitVec {5})))".format(i, j, k, l, config.TEAMBITS*2, config.MATCHBITS)

    def project(self, x, y, z):
        return "round_{0}_match_{1}_slot_{2}".format(x, y, z)

    def read_variable(self, expr1):
        string, = expr1
        regex = "round_([0-9]+)_match_([0-9]+)_slot_([0-9]+)"
        result = re.match(regex, string)
        return int(result.group(1)), int(result.group(2)), int(result.group(3))
