## Yet another SR match scheduler ##

This tools is another attempt to produce a match scheduler for use in the
[Student Robotics](https://studentrobotics.org) competition. The primary
novelty is not that it attempts to produce a schedule according to some
conditions, but that it instead attempts to _describe_ the problem in a logic
format, the solution to which forms a match schedule. Additional 'goodness'
constraints can then be layered on top of this.

The format for this logic is [SMTLIB](http://smtlib.org) v2, which I might just
have become familiar with due to my PhD. The input is a list of variables,
and a list of constraints (assertions) about the values in those variables.
The solver then attempts to find a value assignment to all those variables that
satisfies all of the constraints -- the result is either "satisfiable" (i.e.
there is such an assignment) or "unsatisfiable", meaning there isn't.
The satisfying assignment comes in the form of the values taken by each
variable.

[Numerous solvers](http://smtlib.cs.uiowa.edu/solvers.html) exist for performing
this operation, most of which alas are not fully open source. Z3 is open, but
not under an OSI approved license. Boolector is GPL3, but won't work with the
current formulation of the problem (which could be changed), and might not
currently support extracting the satisfying assignments. CVC{3,4} turns out to
be MIT actually, woot.

The schedule is made in a series of rounds; i.e., we have a small set of matches
in which each team participates once, and the whole schedule is made up of
a number of rounds.  The idea originally came from [the MatchMaker scheduler](http://www.idleloop.com/matchmaker/).

The current list of constraints placed on the schedule:
 * Number of rounds
 * Number of teams (if not a multiple of 4, will probably break excitingly)
 * Teams per match
 * Match seperation distance (i.e., the minimum gap between matches

Some goodness criteria that will be added to see if the solver can generate a
formula that satisfies them are:
 * Distribution of opponents

As for changing these constraints, they're all defined at the start of the
python formula generator. They can be changed, but it's **not really
recommended until some more documentation materialises**. Changing some things
requires the bitwidths of the underlying formula to be changed too; some other
factors such as there being four teams per match, and always a multiple of
four number of teams, are built in at a more fundemental level. Hang around
and these things will be slowly massaged out.

## Usage ##

There are two sets of options that schedule.py will take, covering the constraints placed on the schedule being searched for, and the syntax it's printed in. By default, a schedule for 13 rounds of 4 teams per match, with 32 teams will be printed in the QFBV format. The options are:

 * --rounds N, where N is the number of rounds to schedule
 * --teams N, where N is the number of teams taking part
 * --slots N, where N is the number of teams that can take part in a particular match
 * --closeness X, where X is the minimum number of matches between each teams appearance in the next match

While for syntax:

 * --z3 will produce a formula using Z3 enumerations for identifying teams
 * --qfbv will produce a formula using only bitvector variables
 * --qfaufbv will produce a formula using an uninterpreted function

## Parsing the output ##

At the end of each solver script there are a series of 'get-value' commands, that cause the solver to print out the contents of the schedule it's generated. To convert this to the format the rest of the SR tools expect (pipe separated team names/numbers), the 'readresult.py' script exists. Invoke it with the same options as schedule.py, then pipe the output of the SMT solver into it. It'll then print the schedule in the corresponding SR format.
