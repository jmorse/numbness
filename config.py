import sys

# More flexible parameters
NUMROUNDS = 13                  # How many rounds to schedule in the competition
NUMTEAMS = 32                   # The number of teams taking part
CLOSENESS = 5                   # Minimum number of matches between each teams
                                # appearance.

# More built in parameters.
NUMSLOTS = 4
NUMMATCHES = NUMTEAMS / NUMSLOTS

# Underlying bitwidths
ROUNDBITS = 4
MATCHBITS = 4
SLOTBITS = 2
TEAMBITS = 6

# Validation

if (NUMTEAMS % NUMSLOTS) != 0:
    print >>sys.stderr, "Number of teams does not divide by number of matches"
    sys.exit(1)
