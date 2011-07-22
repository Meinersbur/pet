#include <assert.h>
#include <stdio.h>
#include <isl/arg.h>

#include "scop.h"
#include "scop_yaml.h"

struct options {
	char *scop1;
	char *scop2;
};

struct isl_arg options_arg[] = {
ISL_ARG_ARG(struct options, scop1, "scop1", NULL)
ISL_ARG_ARG(struct options, scop2, "scop2", NULL)
ISL_ARG_END
};

ISL_ARG_DEF(options, struct options, options_arg)

/* Given two YAML descriptions of pet_scops, check whether they
 * represent equivalent scops.
 * If so, return 0.  Otherwise, return 1.
 */
int main(int argc, char **argv)
{
	isl_ctx *ctx;
	struct options *options;
	struct pet_scop *scop1, *scop2;
	FILE *file1, *file2;
	int equal;

	options = options_new_with_defaults();
	assert(options);
	argc = options_parse(options, argc, argv, ISL_ARG_ALL);
	ctx = isl_ctx_alloc_with_options(options_arg, options);

	file1 = fopen(options->scop1, "r");
	assert(file1);
	file2 = fopen(options->scop2, "r");
	assert(file2);

	scop1 = pet_scop_parse(ctx, file1);
	scop2 = pet_scop_parse(ctx, file2);

	equal = pet_scop_is_equal(scop1, scop2);

	pet_scop_free(scop2);
	pet_scop_free(scop1);

	fclose(file2);
	fclose(file1);
	isl_ctx_free(ctx);

	return equal ? 0 : 1;
}
