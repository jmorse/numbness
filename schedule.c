#include <assert.h>
#include <stdbool.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

#include <sys/queue.h>

#define TEAMS_PER_MATCH 4

// SMT structure: only variables are the round variables, identifying what
// teams are in what rounds. Also: an array per round, with the domain the
// team number, and the range the number of matches they've had this round.
//
// Tried to define some structures that munged these things, but it's pointless
// to ensure such rigidity without a proper API: instead, lets just print text
// and store constraints as text.

char scratch_buffer[0x100000]; // 1Mb of text buffer should be enough for anyone

int teams, rounds;
int matches_per_round;

struct constraint;
struct constraint {
	char *string;
	LIST_ENTRY(constraint) entry;
};

// List of contraints we've calculated
LIST_HEAD(, constraint) list_of_constraints;

// Three level array of match schedule variable names; the variables that define
// who is in what match. First index -> the round, second index -> the match,
// and third index -> the participants.
char ****schedule_variable_names;

// Names of arrays storing how many matches a team has had per round.
char **schedule_round_array_names;

// How many times that's been modified over time
int *schedule_round_array_bump_count;

void
usage(const char *progname)
{

	fprintf(stderr, "Usage: %s num_teams num_rounds\n", progname);
	exit(EXIT_FAILURE);
}

void
scratch_to_constraint(void)
{
	struct constraint *c;

	c = malloc(sizeof(*c));
	if (c == NULL) {
		fprintf(stderr, "OOM\n");
		abort();
	}

	c->string = strdup(scratch_buffer);
	LIST_INSERT_HEAD(&list_of_constraints, c, entry);
	return;
}

void
create_round_match_variables(void)
{
	int i, j, k;

	// Lay out match variables, assign names.
	schedule_variable_names = malloc(sizeof(void*) * rounds);
	for (i = 0; i < rounds; i++) {
		schedule_variable_names[i] = malloc(sizeof(void*)
							* matches_per_round);
		for (j = 0; j < matches_per_round; j++) {
			schedule_variable_names[i][j] = malloc(sizeof(int) *
							TEAMS_PER_MATCH);
			for (k = 0; k < TEAMS_PER_MATCH; k++) {
				schedule_variable_names[i][j][k] = malloc(128);
				snprintf(schedule_variable_names[i][j][k], 127,
						"round_%d::match_%d::slot_%d",
						i, j, k);
			}
		}
	}

	// For every round create an array storing how many times we've
	// had a team feature. All initialzed to zero.
	schedule_round_array_bump_count = malloc(sizeof(int) * rounds);
	for (i = 0; i < rounds; i++) {
		sprintf(scratch_buffer, "round_%d_team_array#0", i);
		schedule_round_array_names[i] = strdup(scratch_buffer);
		schedule_round_array_bump_count[i] = 0;
	}

	return;
}

void
create_round_correct_constraints(void)
{
	int i, j, k;

	// The constraints: that teams only appear once in the round (which
	// also ensures they don't appear more than once in the same match),
	// and that they /do/ appear in the round.

	// Start off by constraining each match entry to be in the range of
	// permissable teams.

	for (i = 0; i < rounds; i++) {
		for (j = 0; j < matches_per_round; j++) {
			for (k = 0; k < TEAMS_PER_MATCH; k++) {
				sprintf(scratch_buffer, "(assert (>= %s 0))\n",
					schedule_variable_names[i][j][k]);
				scratch_to_constraint();
			}
		}
	}

	// Next up, ensuring we have each team once per round. We could assert
	// they occur at least once with a huge 'or', and then count those
	// occurences to ensure it's only as many as rounds there are, but
	// that's unlikely to be an efficient structure. How about one array
	// per round, fields nondeterministically updated, must all equal one?
	// That probably works and scales.

	// For each round, store zeros in each element per team, by assertion.
	for (i = 0; i < rounds; i++) {
		for (j = 0; j < teams; j++) {
			char *name = schedule_round_array_names[i];
			sprintf(scratch_buffer,
					"(assert (= 0 (select %s %d)))\n",
					name, j);
			scratch_to_constraint();
		}
	}

	// Now for each team in each match, increment the corresponding element
	// by one.
	for (i = 0; i < rounds; i++) {
		for (j = 0; j < matches_per_round; j++) {
			for (k = 0; k < TEAMS_PER_MATCH; k++) {
				// Do something
			}
		}
	}


	assert(0);
}

void
create_goodness_constraints(void)
{

	// Goodness: that teams have the same number of matches, that they have
	// some good distance between matches, that they face a reasonable
	// range of other teams.
	assert(0);
}

void
create_constraints(void)
{

	create_round_match_variables();
	create_round_correct_constraints();
	create_goodness_constraints();
}

void
print_to_solver(void)
{

	assert(0);
}

void
solve_with_solver(void)
{

	assert(0);
}

void
display_solved_model(void)
{

	assert(0);
}

int
main(int argc, char **argv)
{

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

	matches_per_round = teams / rounds;
	if (teams % rounds != 0)
		matches_per_round++;

	// Produce constraints ast
	create_constraints();

	// Pretty print those constraints to a solver
	print_to_solver();

	// Invoke the solver and get a result (or, perhaps, time out)
	solve_with_solver();

	// Extract the model of the schedule and print it.
	display_solved_model();

	exit(EXIT_SUCCESS);
}
