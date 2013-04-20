#include <assert.h>
#include <stdbool.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

#include <sys/queue.h>

#define TEAMS_PER_MATCH 4
#define MATCH_SEPARATION 2
#define MEET_SPREADING_RATE 0.5

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

// The actual schedule, once read from solver.
int ***match_outcomes;

// Not storing met-team variable names globally because they're likely to be
// fairly transient.

void
usage(const char *progname)
{

	fprintf(stderr, "Usage: %s num_teams num_rounds\n", progname);
	exit(EXIT_FAILURE);
}

void
del_output_file(void)
{

	unlink(output_file_name);
}


void
del_input_file(void)
{

	unlink(input_file_name);
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
	int i, j, k;

	// Goodness: that teams have the same number of matches, that they have
	// some good distance between matches, that they face a reasonable
	// range of other teams.

	// Rather than trying to calculate numbers of matches using integer
	// addition, which is relatively expensive, we can in fact just use
	// distinct again: ensure that, across the edges of rounds, all the
	// teams playing are distinct. This preserves the condition that matches
	// are sufficiently seperate over that period, without resorting to
	// any additional logic.

	// So: for each N-match period that covers the boundry of a round,
	// apply a distinct to all the slots in it.

	assert(MATCH_SEPARATION < matches_per_round && "Match seperation "
		       "requirement prohibits all schedules");

	for (i = 0; i < rounds - 1; i++) { // For each boundry...
		// early_match_pos is the match to start this period at in the
		// earlier match; later_match_pos is the position in the later
		// match at which to stop this period.
		int early_match_pos, later_match_pos;

		// Start with the period we cover overlapping mostly the earlier
		// round and only covering one match in the later round; then
		// move across the boundry match by match.
		for (early_match_pos = matches_per_round - MATCH_SEPARATION,
				later_match_pos = 1;
				early_match_pos < matches_per_round;
				early_match_pos++, later_match_pos++) {

			// Over this range, cover MATCH_SEPARATION + 1 matches,
			// to ensure that after having one match we don't have
			// a match in the subsequent MATCH_SEPARATION matches.
			sprintf(scratch_buffer,  "(assert (distinct ");

			// Early portion
			for (j = early_match_pos; j < matches_per_round; j++) {
				for (k = 0; k < TEAMS_PER_MATCH; k++) {
					strcat(scratch_buffer,
					schedule_variable_names[i][j][k]);
					strcat(scratch_buffer, " ");
				}
			}

			// Later portion
			for (j = 0; j < later_match_pos; j++) {
				for (k = 0; k < TEAMS_PER_MATCH; k++) {
					strcat(scratch_buffer,
					schedule_variable_names[i+1][j][k]);
					strcat(scratch_buffer, " ");
				}
			}

			strcat(scratch_buffer, "))\n");

			scratch_to_constraint();
		} // End of one period
	} // End of one round boundry

	// Facing a range of teams -- this is fundementally a rounds/teams
	// ratio, seeing how 3 rounds with 100 teams won't allow you to meet
	// everyone.
	//
	// So instead, we'll attempt to measure it as a proportion of the
	// number of teams versus the number of teams you can face. There's
	// no way to just 'optimise for this', we set a minimum and see if
	// it's satisfiable. Floating point arith becomes necessary, alas,
	// but we can keep it out of the formula. The range is from zero
	// (no attempt to make you meet people) to 1.0 (meet everyone).
	//
	// After ensuring you've met everyone, another facet is ensuring you
	// don't meet the same people repeatedly, which can be addressed later
	// (and is likely to be much easier).
	
	// How to encode this? Can't think of a clever way, so go for the stupid
	// way: one array per team, nondeterminsitically increment elements in
	// each array every round, apply assertions at the end. Probably going
	// to be horrible for performance; best we can hope for is that it
	// reduces the state space to search.

	// Calculate minimum number of people to meet, truncated
	//int min_people_met = teams * MEET_SPREADING_RATE;

#if 0
	// Create some tracking arrays, zero initialize them.
	for (i = 0; i < teams; i++) {
		int elemcount = 0;
		sprintf(scratch_buffer, "met_teams_%d_array_round_Z_slot_Z", i);
		char *oldname = strdup(scratch_buffer);
		char *newname = NULL;

		for (elemcount = 0; elemcount < teams; elemcount++) {
			sprintf(scratch_buffer,
					"met_teams_%d_array_round_Z_slot_%d",
					i, elemcount);
			newname = strdup(scratch_buffer);

			// Store into the old buffer, at element elemcount,
			// the value zero.
			sprintf(scratch_buffer,
					"(assert (= %s (store %s %d 0)))",
					oldname, newname, elemcount);
			scratch_to_constraint();
			free(oldname);
			oldname = newname;
		}

		free(oldname);
	}
#endif

#if 0
	// Now that we're zero inited, start putting some increments in there.
	// Quite a number, unfortunately.
	for (i = 0; i < rounds; i++) {
		for (j = 0; j < matches_per_round; j++) {
			for (k = 0; k < TEAMS_PER_MATCH; k++) {
				// For each /other/ team in the match, encode
				// an addition.
				int l;
				for (l = 0; l < TEAMS_PER_MATCH; l++) {
					if (l == k)
						continue;
#endif

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
	if (fd < 0) {
		perror("Couldn't open formula output file");
		exit(EXIT_FAILURE);
	}

	atexit(del_output_file);
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

	// Fetch all variables
	for (i = 0; i < rounds; i++) {
		for (j = 0; j < matches_per_round; j++) {
			for (k = 0; k < TEAMS_PER_MATCH; k++) {
				fprintf(outfile, "(get-value (%s))\n",
					schedule_variable_names[i][j][k]);
			}
		}
	}

	fclose(outfile);
	fprintf(stderr, "Done generating benchmark, at %s\n", output_file_name);
}

void
solve_with_solver(void)
{
	int fd, result;

	// Rather than attempting to stream gunge into the solver and
	// dynamically ask it questions about what it solved, for the moment
	// just feed it the output file it wrote, then parse the get-model
	// output. Assume, for now, Z3.

	fd = mkstemp(input_file_name);
	if (fd < 0) {
		perror("Couldn't create solver-output-file");
		exit(EXIT_FAILURE);
	}
	close(fd);
	atexit(del_input_file);

	sprintf(scratch_buffer,"/home/jmorse/phd/cvc/cvc4-1.0-x86_64-linux-opt --smtlib-strict %s > %s",
			output_file_name, input_file_name);
	result = system(scratch_buffer);
	if (result == -1) {
		perror("Couldn't fork to run solver");
		exit(EXIT_FAILURE);
	}

	if (!WIFEXITED(result)) {
		fprintf(stderr, "Solver exited abnormally, you broke it\n");
		exit(EXIT_FAILURE);
	}

	// CVC elects to return 10 on SAT result, the rapscallion.
	if (WEXITSTATUS(result) != 10) {
		fprintf(stderr, "Solver exited with status %d, SMT syntax "
				"probably broken, please inspect\n",
				WEXITSTATUS(result));
		exit(EXIT_FAILURE);
	}

	// Past here, solver returned successfully.
	return;
}

void
display_solved_model(void)
{
	char formatted_output[] = "/tmp/sr_sched_reformatted_XXXXXX";
	FILE *file;
	int status, fd, round, match, slot, team, i, j, k;

	// Rather than writing a proper parser and attempting to interpret
	// all of these things, go for the half-arsed "work on the way Z3 prints
	// it" approach. Which is fine for now.

	fd = mkstemp(formatted_output);
	if (fd < 0) {
		perror("Couldn't open formatted output file");
		exit(EXIT_FAILURE);
	}
	close(fd);

	// Pump the Z3 output through a useful awk script
	sprintf(scratch_buffer, "./smt_parse.awk < %s > %s", input_file_name,
			formatted_output);
	status = system(scratch_buffer);
	if (status == -1) {
		perror("Couldn't fork to parse output");
		unlink(formatted_output);
		exit(EXIT_FAILURE);
	}

	if (!WIFEXITED(status)) {
		fprintf(stderr, "Awk exited abnormally\n");
		unlink(formatted_output);
		exit(EXIT_FAILURE);
	}

	if (WEXITSTATUS(status) != 0) {
		fprintf(stderr, "Awk exited with status %d\n",
				WEXITSTATUS(status));
		unlink(formatted_output);
		exit(EXIT_FAILURE);
	}

	// Success.

	file = fopen(formatted_output, "r");
	if (file == NULL) {
		perror("Couldn't open formatted output");
		unlink(formatted_output);
		exit(EXIT_FAILURE);
	}

	// Grab some memory.
	match_outcomes = malloc(sizeof(int *) * rounds);
	for (i = 0; i < rounds; i++) {
		match_outcomes[i] = malloc(sizeof(int *) * matches_per_round);
		for (j = 0; j < matches_per_round; j++) {
			match_outcomes[i][j] =
				malloc(sizeof(int) * TEAMS_PER_MATCH);
		}
	}

	while (fscanf(file, "((round_%d_match_%d_slot_%d %d))\n", &round,&match,
				&slot, &team) == 4) {
		// Store for later printing
		assert(round >= 0 && round < rounds);
		assert(match >= 0 && match < matches_per_round);
		assert(slot >= 0 && slot < TEAMS_PER_MATCH);
		assert(team >= 0 && team < teams);
		match_outcomes[round][match][slot] = team;
	}
	fclose(file);
	unlink(formatted_output);

	// Now print that data in some kind of order.
	for (i = 0; i < rounds; i++) {
		for (j = 0; j < matches_per_round; j++) {
			printf("%d", match_outcomes[i][j][0]);
			for (k = 1; k < TEAMS_PER_MATCH; k++) {
				printf("|%d", match_outcomes[i][j][k]);
			}
			printf("\n");
		}
	}
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
