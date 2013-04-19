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

	// Do some stuff
	exit(EXIT_SUCCESS);
}
