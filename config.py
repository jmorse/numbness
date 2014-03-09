import sys
from math import log, ceil

global NUMROUNDS, NUMTEAMS, CLOSENESS, NUMSLOT

# More flexible parameters
NUMROUNDS = 13                  # How many rounds to schedule in the competition
NUMTEAMS = 32                   # The number of teams taking part
CLOSENESS = 5                   # Minimum number of matches between each teams
                                # appearance.

# More built in parameters.
NUMSLOTS = 4                    # Everything will break if this changes.
                                # That's fine, because SR doesn't use any other
                                # match format for the moment.

def compute_bitwidths():
    global NUMMATCHES, ROUNDBITS, MATCHBITS, SLOTBITS, TEAMBITS
    NUMMATCHES = NUMTEAMS / NUMSLOTS

    # Underlying bitwidths, computed from other parameters
    ROUNDBITS = int(ceil(log(NUMROUNDS, 2)))
    MATCHBITS = int(ceil(log(NUMMATCHES, 2)))
    SLOTBITS = int(ceil(log(NUMSLOTS, 2)))
    TEAMBITS = int(ceil(log(NUMTEAMS, 2)))

compute_bitwidths()

# Validation

def validate_config():
    if (NUMTEAMS % NUMSLOTS) != 0:
        print >>sys.stderr, "Num of teams does not divide by number of matches"
        sys.exit(1)

    if CLOSENESS >= NUMMATCHES:
        print >>sys.stderr, "Match close constraints allows no matches"
        sys.exit(1)

validate_config()
