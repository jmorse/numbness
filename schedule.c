#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

#include <sys/queue.h>

#define TEAMS_PER_MATCH 4

// SMT structure: only variables are the round variables, identifying what
// teams are in what rounds.
// Formulas are all of integer or bool types; operations are only the normal
// integer relations and equality. Operands are only ever one of the round
// variables or a integer constant.

enum operations {
	op_equality = 0,
	op_notequal,
	op_lessthan,
	op_lessthanequal,
	op_greaterthan,
	op_greaterthanequal,
};

union operand {
	char *variable_name;
	unsigned int constant_num;
};

struct constraint {
	enum operations op;
	union operand operand1;
	union operand operand2;
	bool op1_is_variable, op2_is_variable;
};

int teams, rounds;
int matches_per_round;

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

	return;
}

void
create_round_correct_constraints(void)
{

	// The constraints: that teams only appear once in the round (which
	// also ensures they don't appear more than once in the same match),
	// and that they /do/ appear in the round.

	assert(0);
}

void
create_goodness_constraints(void)
{

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
