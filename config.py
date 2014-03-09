import sys
from math import log, ceil

NUMROUNDS = 13
NUMTEAMS = 32
CLOSENESS = 5
NUMSLOTS = 4

NUMMATCHES = 0
ROUNDBITS = 0
MATCHBITS = 0
SLOTBITS = 0
TEAMBITS = 0

def set_config(rounds, teams, closeness):
    global NUMROUNDS, NUMTEAMS, CLOSENESS, NUMSLOTS
    print rounds
    NUMROUNDS = rounds     # How many rounds to schedule in the competition
    NUMTEAMS = teams       # The number of teams taking part
    CLOSENESS = closeness  # Minimum number of matches between each teams
                           # appearance.

    NUMSLOTS = 4           # Everything will break if this changes.
                           # That's fine, because SR doesn't use any
                           # other  match format for the moment.

def compute_bitwidths():
    global NUMROUNDS, NUMTEAMS, CLOSENESS, NUMSLOTS
    global NUMMATCHES, ROUNDBITS, MATCHBITS, SLOTBITS, TEAMBITS
    print "fgasdf"
    print NUMMATCHES
    NUMMATCHES = NUMTEAMS / NUMSLOTS
    print NUMMATCHES

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
