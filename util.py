from config import *

def print_integer(val, width):
        return "(_ bv{0} {1})".format(val, width)

def sparticus(r, match, slot):
        return "(sparticus {0} {1} {2})".format(print_integer(r, ROUNDBITS),
                        print_integer(match, MATCHBITS),
                        print_integer(slot, SLOTBITS))
