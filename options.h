#include <isl/arg.h>
#include <isl/ctx.h>

#if defined(__cplusplus)
extern "C" {
#endif

struct pet_options {
	int	autodetect;
	int	n_path;
	const char **paths;
};

ISL_ARG_CTX_DECL(pet_options, struct pet_options, pet_options_args)

#if defined(__cplusplus)
}
#endif
