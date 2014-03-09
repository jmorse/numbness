import sys
from math import log, ceil

# More flexible parameters
NUMROUNDS = 13                  # How many rounds to schedule in the competition
NUMTEAMS = 32                   # The number of teams taking part
CLOSENESS = 5                   # Minimum number of matches between each teams
                                # appearance.

# More built in parameters.
NUMSLOTS = 4                    # Everything will break if this changes.
                                # That's fine, because SR doesn't use any other
                                # match format for the moment.
NUMMATCHES = NUMTEAMS / NUMSLOTS

# Underlying bitwidths, computed from other parameters
ROUNDBITS = int(ceil(log(NUMROUNDS, 2)))  # Num bits required for n rounds
MATCHBITS = int(ceil(log(NUMMATCHES, 2))) # Same, for matches
SLOTBITS = int(ceil(log(NUMSLOTS, 2)))    # ...
TEAMBITS = int(ceil(log(NUMTEAMS, 2)))    # ...

# Validation

if (NUMTEAMS % NUMSLOTS) != 0:
    print >>sys.stderr, "Number of teams does not divide by number of matches"
    sys.exit(1)
