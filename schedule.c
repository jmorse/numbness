#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

#define TEAMS_PER_MATCH 4

void
usage(const char *progname)
{

	fprintf(stderr, "Usage: %s num_teams num_rounds\n", progname);
	exit(EXIT_FAILURE);
}

int
main(int argc, char **argv)
{
	int teams, rounds;

	if (argc != 3)
		usage(argv[0]);

	teams = atoi(argv[1]);
	if (teams < TEAMS_PER_MATCH) {
		fprintf(stderr, "%d is not an acceptable number of teams\n",
				teams);
		exit(EXIT_FAILURE);
	}

	rounds = atoi(argv[2]);
	if (rounds < 0) {
		fprintf(stderr, "%d is not an acceptable number of rounds\n",
				rounds);
		exit(EXIT_FAILURE);
	}

	// Produce constraints ast
	// Insert here: some SMT generation tool

	// Pretty print those constraints to a solver
	// Insert here: that

	// Invoke the solver and get a result (or, perhaps, time out)
	// La la la

	// Extract the model of the schedule and print it.
	// Ta ta ta

	exit(EXIT_SUCCESS);
}
