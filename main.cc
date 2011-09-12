/*
 * Copyright 2011 Leiden University. All rights reserved.
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
 * THIS SOFTWARE IS PROVIDED BY LEIDEN UNIVERSITY ''AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL LEIDEN UNIVERSITY OR
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
 * Leiden University.
 */ 

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
