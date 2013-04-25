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
a number of rounds. The idea originally came from Rob, he's probably written
it down somewhere.

The current list of constraints placed on the schedule:
 * Number of rounds
 * Number of teams (if not a multiple of 4, will probably break excitingly)
 * Teams per match, currently 4
 * Match seperation distance, currently 2

Some goodness criteria that will be added to see if the solver can generate a
formula that satisfies them are:
 * Distribution of opponents

As for changing these constraints, they're all defined at the start of the
python formula generator. They can be changed, but it's '''not really
recommended until some more documentation materialises'''. Changing some things
requires the bitwidths of the underlying formula to be changed too; some other
factors such as there being four teams per match, and always a multiple of
four number of teams, are built in at a more fundemental level. Hang around
and these things will be slowly massaged out.
