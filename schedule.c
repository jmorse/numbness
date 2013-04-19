#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

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

void
usage(const char *progname)
{

	fprintf(stderr, "Usage: %s num_teams num_rounds\n", progname);
	exit(EXIT_FAILURE);
}

void
create_round_match_variables(void)
{

	assert(0);
}

void
create_round_correct_constraints(void)
{

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
	create_constraints();

	// Pretty print those constraints to a solver
	print_to_solver();

	// Invoke the solver and get a result (or, perhaps, time out)
	solve_with_solver();

	// Extract the model of the schedule and print it.
	display_solved_model();

	exit(EXIT_SUCCESS);
}
