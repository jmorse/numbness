#include <assert.h>
#include <stdbool.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

#include <sys/queue.h>

#define TEAMS_PER_MATCH 4

// SMT structure: only variables are the round variables, identifying what
// teams are in what rounds.
//
// Tried to define some structures that munged these things, but it's pointless
// to ensure such rigidity without a proper API: instead, lets just print text
// and store constraints as text.

char scratch_buffer[0x100000]; // 1Mb of text buffer should be enough for anyone

int teams, rounds;
int matches_per_round;

// File where we'll be writing all the output gunge to
char output_file_name[] = "/tmp/sr_schedule_XXXXXX";
char input_file_name[] = "/tmp/sr_sched_solution_XXXXXX";

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
						"round_%d_match_%d_slot_%d",
						i, j, k);
			}
		}
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
				sprintf(scratch_buffer, "(assert (< %s %d))\n",
					schedule_variable_names[i][j][k],
					teams);
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

	// Or we could just state that they're all distinct...

	for (i = 0; i < rounds; i++) {
		sprintf(scratch_buffer, "(assert (distinct ");
		for (j = 0; j < matches_per_round; j++) {
			for (k = 0; k < TEAMS_PER_MATCH; k++) {
				strcat(scratch_buffer,
					schedule_variable_names[i][j][k]);
				strcat(scratch_buffer, " ");
			}
		}

		strcat(scratch_buffer, "))\n");

		scratch_to_constraint();
	}


	return;
}

void
create_goodness_constraints(void)
{

	// Goodness: that teams have the same number of matches, that they have
	// some good distance between matches, that they face a reasonable
	// range of other teams.

	// As of this moment, no goodness constraints. Just testing.
	return;
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
	int fd, i, j, k;
	FILE *outfile;
	struct constraint *ptr;

	// Spawn Z3; feed formula. Worry about using a properly open source
	// solver in the future.

	// Worry about streaming data into it later if we get onto incremental
	// SMT.

	fd = mkstemp(output_file_name);
	outfile = fdopen(fd, "w");
	fprintf(outfile, "(set-info :status unknown)\n");
	fprintf(outfile, "(set-option :produce-models true)\n");
	fprintf(outfile, "(set-logic QF_AUFLIRA)\n");

	// Declare a bunch of symbols,

	// The round variables
	for (i = 0; i < rounds; i++) {
		for (j = 0; j < matches_per_round; j++) {
			for (k = 0; k < TEAMS_PER_MATCH; k++) {
				fprintf(outfile, "(declare-fun %s () Int)\n",
					schedule_variable_names[i][j][k]);
			}
		}
	}

	// Now start pumping out constraints
	LIST_FOREACH(ptr, &list_of_constraints, entry) {
		fprintf(outfile, "%s", ptr->string);
	}

	fprintf(outfile, "(check-sat)\n");
	fprintf(outfile, "(get-model)\n");

	fclose(outfile);
	printf("Done generating benchmark, at %s\n", output_file_name);
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

	matches_per_round = teams / TEAMS_PER_MATCH;
	if (teams % TEAMS_PER_MATCH != 0)
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
