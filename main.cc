#include <string>
#include <llvm/Support/CommandLine.h>

#include <isl/ctx.h>

#include "scop.h"
#include "scop_yaml.h"

using namespace std;

static llvm::cl::opt<string> InputFilename(llvm::cl::Positional,
			llvm::cl::Required, llvm::cl::desc("<input file>"));
static llvm::cl::opt<bool> AutoDetect("autodetect",
			llvm::cl::desc("Autodetect scops"));

int main(int argc, char *argv[])
{
	isl_ctx *ctx = isl_ctx_alloc();
	pet_scop *scop;

	llvm::cl::ParseCommandLineOptions(argc, argv);

	scop = pet_scop_extract_from_C_source(ctx, InputFilename.c_str(), NULL,
						AutoDetect);

	if (scop)
		pet_scop_emit(stdout, scop);

	pet_scop_free(scop);

	isl_ctx_free(ctx);
	return 0;
}
