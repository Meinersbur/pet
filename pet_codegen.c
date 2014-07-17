/*
 * Copyright 2012 Ecole Normale Superieure. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *    1. Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *    2. Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY ECOLE NORMALE SUPERIEURE ''AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL ECOLE NORMALE SUPERIEURE OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * The views and conclusions contained in the software and documentation
 * are those of the authors and should not be interpreted as
 * representing official policies, either expressed or implied, of
 * Ecole Normale Superieure.
 */

#include <assert.h>
#include <isl/aff.h>
#include <isl/ast_build.h>
#include <isl/options.h>
#include <isl/set.h>
#include <isl/map.h>

struct options {
	struct isl_options	*isl;
	unsigned		 atomic;
	unsigned		 separate;
	unsigned		 read_options;
};

ISL_ARGS_START(struct options, options_args)
ISL_ARG_CHILD(struct options, isl, "isl", &isl_options_args, "isl options")
ISL_ARG_BOOL(struct options, atomic, 0, "atomic", 0,
	"globally set the atomic option")
ISL_ARG_BOOL(struct options, separate, 0, "separate", 0,
	"globally set the separate option")
ISL_ARG_BOOL(struct options, read_options, 0, "read-options", 0,
	"read options from standard input")
ISL_ARGS_END

ISL_ARG_DEF(options, struct options, options_args)

/* Return a universal, 1-dimensional set with the given name.
 */
static __isl_give isl_union_set *universe(isl_ctx *ctx, const char *name)
{
	isl_space *space;

	space = isl_space_set_alloc(ctx, 0, 1);
	space = isl_space_set_tuple_name(space, isl_dim_set, name);
	return isl_union_set_from_set(isl_set_universe(space));
}

/* Set the "name" option for the entire schedule domain.
 */
static __isl_give isl_union_map *set_universe(__isl_take isl_union_map *opt,
	__isl_keep isl_union_map *schedule, const char *name)
{
	isl_ctx *ctx;
	isl_union_set *domain, *target;
	isl_union_map *option;

	ctx = isl_union_map_get_ctx(opt);

	domain = isl_union_map_range(isl_union_map_copy(schedule));
	domain = isl_union_set_universe(domain);
	target = universe(ctx, name);
	option = isl_union_map_from_domain_and_range(domain, target);
	opt = isl_union_map_union(opt, option);

	return opt;
}

/* Set the build options based on the command line options.
 *
 * If no command line options are specified, we use default build options.
 * If --read-options is specified, we read the build options from standard
 * input.
 * If --separate or --atomic is specified, we turn on the corresponding
 * build option over the entire schedule domain.
 */
static __isl_give isl_ast_build *set_options(__isl_take isl_ast_build *build,
	struct options *options, __isl_keep isl_union_map *schedule)
{
	isl_ctx *ctx;
	isl_space *space;
	isl_union_set *domain, *separate;
	isl_union_map *opt, *opt_s, *opt_a;

	if (!options->separate && !options->atomic && !options->read_options)
		return build;

	ctx = isl_union_map_get_ctx(schedule);

	if (options->read_options)
		opt = isl_union_map_read_from_file(ctx, stdin);
	else
		opt = isl_union_map_empty(isl_union_map_get_space(schedule));

	if (options->separate)
		opt = set_universe(opt, schedule, "separate");
	if (options->atomic)
		opt = set_universe(opt, schedule, "atomic");

	build = isl_ast_build_set_options(build, opt);

	return build;
}

/* Print a function declaration for the domain "set".
 *
 * In particular, print a declaration of the form
 *
 *	void S(int, ..., int);
 *
 * where S is the name of the domain and the number of arguments
 * is equal to the dimension of "set".
 */
static int print_declaration(__isl_take isl_set *set, void *user)
{
	isl_printer **p = user;
	int i, n;

	n = isl_set_dim(set, isl_dim_set);

	*p = isl_printer_start_line(*p);
	*p = isl_printer_print_str(*p, "void ");
	*p = isl_printer_print_str(*p, isl_set_get_tuple_name(set));
	*p = isl_printer_print_str(*p, "(");
	for (i = 0; i < n; ++i) {
		if (i)
			*p = isl_printer_print_str(*p, ", ");
		*p = isl_printer_print_str(*p, "int");
	}
	*p = isl_printer_print_str(*p, ");");
	*p = isl_printer_end_line(*p);

	isl_set_free(set);

	return 0;
}

/* Print a function declaration for each domain in "uset".
 */
static __isl_give isl_printer *print_declarations(__isl_take isl_printer *p,
	__isl_keep isl_union_set *uset)
{
	if (isl_union_set_foreach_set(uset, &print_declaration, &p) >= 0)
		return p;
	isl_printer_free(p);
	return NULL;
}

/* Check that the domain of "map" is named.
 */
static int check_name(__isl_take isl_map *map, void *user)
{
	int named;
	isl_ctx *ctx;

	ctx = isl_map_get_ctx(map);
	named = isl_map_has_tuple_name(map, isl_dim_in);
	isl_map_free(map);

	if (named < 0)
		return -1;
	if (!named)
		isl_die(ctx, isl_error_invalid,
			"all domains should be named", return -1);
	return 0;
}

/* Read a schedule, a context and (optionally) build options,
 * generate an AST and print the result in a form that is readable
 * by pet.
 *
 * In particular, print out the following code
 *
 *	void foo(<parameters>/)
 *	{
 *		void S1(int,...,int);
 *	#pragma scop
 *		AST
 *	#pragma endscop
 *	}
 */
int main(int argc, char **argv)
{
	int i, n;
	isl_ctx *ctx;
	isl_set *context;
	isl_union_set *domain;
	isl_union_map *schedule;
	isl_ast_build *build;
	isl_ast_node *tree;
	struct options *options;
	isl_ast_print_options *print_options;
	isl_printer *p;

	options = options_new_with_defaults();
	assert(options);
	argc = options_parse(options, argc, argv, ISL_ARG_ALL);

	ctx = isl_ctx_alloc_with_options(&options_args, options);

	schedule = isl_union_map_read_from_file(ctx, stdin);
	if (isl_union_map_foreach_map(schedule, &check_name, NULL) < 0) {
		isl_union_map_free(schedule);
		isl_ctx_free(ctx);
		return 1;
	}
	context = isl_set_read_from_file(ctx, stdin);
	context = isl_set_align_params(context,
					isl_union_map_get_space(schedule));

	domain = isl_union_map_domain(isl_union_map_copy(schedule));

	p = isl_printer_to_file(ctx, stdout);
	p = isl_printer_set_output_format(p, ISL_FORMAT_C);
	p = isl_printer_start_line(p);
	p = isl_printer_print_str(p, "void foo(");

	n = isl_set_dim(context, isl_dim_param);
	for (i = 0; i < n; ++i) {
		const char *name;
		if (i)
			p = isl_printer_print_str(p, ", ");
		name = isl_set_get_dim_name(context, isl_dim_param, i);
		p = isl_printer_print_str(p, "int ");
		p = isl_printer_print_str(p, name);
	}

	p = isl_printer_print_str(p, ")");
	p = isl_printer_end_line(p);
	p = isl_printer_start_line(p);
	p = isl_printer_print_str(p, "{");
	p = isl_printer_end_line(p);
	p = isl_printer_start_line(p);
	p = isl_printer_indent(p, 2);
	p = print_declarations(p, domain);
	p = isl_printer_indent(p, -2);
	p = isl_printer_print_str(p, "#pragma scop");
	p = isl_printer_end_line(p);

	build = isl_ast_build_from_context(context);
	build = set_options(build, options, schedule);
	tree = isl_ast_build_node_from_schedule_map(build, schedule);
	isl_ast_build_free(build);

	p = isl_printer_indent(p, 2);
	print_options = isl_ast_print_options_alloc(ctx);
	p = isl_ast_node_print(tree, p, print_options);
	p = isl_printer_indent(p, -2);
	p = isl_printer_start_line(p);
	p = isl_printer_print_str(p, "#pragma endscop");
	p = isl_printer_end_line(p);
	p = isl_printer_start_line(p);
	p = isl_printer_print_str(p, "}");
	p = isl_printer_end_line(p);
	isl_printer_free(p);

	isl_ast_node_free(tree);
	isl_union_set_free(domain);
	isl_ctx_free(ctx);
	return 0;
}
