import sys
from math import log, ceil

def set_config(rounds, teams, closeness, slots):
    global NUMROUNDS, NUMTEAMS, CLOSENESS, NUMSLOTS
    NUMROUNDS = rounds     # How many rounds to schedule in the competition
    NUMTEAMS = teams       # The number of teams taking part
    CLOSENESS = closeness  # Minimum number of matches between each teams
                           # appearance.

    NUMSLOTS = slots       # Number of slots per match

def compute_bitwidths():
    global NUMROUNDS, NUMTEAMS, CLOSENESS, NUMSLOTS
    global NUMMATCHES, ROUNDBITS, MATCHBITS, SLOTBITS, TEAMBITS
    NUMMATCHES = NUMTEAMS / NUMSLOTS

    # Underlying bitwidths, computed from other parameters
    ROUNDBITS = int(ceil(log(NUMROUNDS, 2)))
    MATCHBITS = int(ceil(log(NUMMATCHES, 2)))
    SLOTBITS = int(ceil(log(NUMSLOTS, 2)))
    TEAMBITS = int(ceil(log(NUMTEAMS, 2)))

# Validation

def validate_config():
    global NUMROUNDS, NUMTEAMS, CLOSENESS, NUMSLOTS
    if (NUMTEAMS % NUMSLOTS) != 0:
        print >>sys.stderr, "Num of teams does not divide by number of matches"
        sys.exit(1)

    if CLOSENESS >= NUMMATCHES:
        print >>sys.stderr, "Match close constraints allows no matches"
        sys.exit(1)

    if (NUMSLOTS % 4) != 0:
        print >>sys.stderr, "Number of slots is not a multiple of four. The world will end."
        sys.exit(1)
