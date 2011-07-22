#include <stdlib.h>
#include <map>
#include <iostream>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/ManagedStatic.h>
#include <llvm/Support/Host.h>
#include <clang/Basic/Version.h>
#include <clang/Basic/FileSystemOptions.h>
#include <clang/Basic/FileManager.h>
#include <clang/Basic/TargetOptions.h>
#include <clang/Basic/TargetInfo.h>
#include <clang/Frontend/CompilerInvocation.h>
#include <clang/Frontend/DiagnosticOptions.h>
#include <clang/Frontend/TextDiagnosticPrinter.h>
#include <clang/Frontend/HeaderSearchOptions.h>
#include <clang/Frontend/LangStandard.h>
#include <clang/Frontend/PreprocessorOptions.h>
#include <clang/Frontend/FrontendOptions.h>
#include <clang/Frontend/Utils.h>
#include <clang/Lex/HeaderSearch.h>
#include <clang/Lex/Preprocessor.h>
#include <clang/Lex/Pragma.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/ASTConsumer.h>
#include <clang/Sema/Sema.h>
#include <clang/Sema/SemaDiagnostic.h>
#include <clang/Parse/Parser.h>
#include <clang/Parse/ParseAST.h>

#include <isl/ctx.h>
#include <isl/constraint.h>

#include "scan.h"

#include "config.h"

#define ARRAY_SIZE(array) (sizeof(array)/sizeof(*array))

using namespace std;
using namespace clang;

/* Called if we found something we didn't expect in one of the pragmas.
 * We'll provide more informative warnings later.
 */
static void unsupported(Preprocessor &PP, SourceLocation loc)
{
	Diagnostic &diag = PP.getDiagnostics();
	unsigned id = diag.getCustomDiagID(Diagnostic::Warning, "unsupported");
	DiagnosticBuilder B = diag.Report(loc, id);
}

/* Set the lower and upper bounds on the given dimension of "set"
 * to "lb" and "ub".
 */
static __isl_give isl_set *set_bounds(__isl_take isl_set *set,
	enum isl_dim_type type, int pos, int lb, int ub)
{
	isl_constraint *c;

	c = isl_inequality_alloc(isl_set_get_dim(set));
	isl_constraint_set_coefficient_si(c, type, pos, 1);
	isl_constraint_set_constant_si(c, -lb);
	set = isl_set_add_constraint(set, c);

	c = isl_inequality_alloc(isl_set_get_dim(set));
	isl_constraint_set_coefficient_si(c, type, pos, -1);
	isl_constraint_set_constant_si(c, ub);
	set = isl_set_add_constraint(set, c);

	return set;
}

static int get_int(const char *s)
{
	return s[0] == '"' ? atoi(s + 1) : atoi(s);
}

/* Handle pragmas of the form
 *
 *	#pragma value_bounds identifier lower_bound upper_bound
 *
 * For each such pragma, add a mapping from the ValueDecl corresponding
 * to "identifier" to a set { [i] : lower_bound <= i <= upper_bound }
 * to the map value_bounds.
 */
struct PragmaValueBoundsHandler : public PragmaHandler {
	Sema &sema;
	isl_ctx *ctx;
	map<ValueDecl *, isl_set *> &value_bounds;

	PragmaValueBoundsHandler(isl_ctx *ctx, Sema &sema,
				map<ValueDecl *, isl_set *> &value_bounds) :
		PragmaHandler("value_bounds"), ctx(ctx), sema(sema),
		value_bounds(value_bounds) {}

	virtual void HandlePragma(Preprocessor &PP,
				  PragmaIntroducerKind Introducer,
				  Token &ScopTok) {
		isl_dim *dim;
		isl_set *set;
		IdentifierInfo *name;
		Decl *decl;
		ValueDecl *vd;
		Token token;
		int lb;
		int ub;

		PP.Lex(token);
		if (token.isNot(tok::identifier)) {
			unsupported(PP, token.getLocation());
			return;
		}

		name = token.getIdentifierInfo();
		decl = sema.LookupSingleName(sema.TUScope, name,
				token.getLocation(), Sema::LookupOrdinaryName);
		vd = decl ? cast_or_null<ValueDecl>(decl) : NULL;
		if (!vd) {
			unsupported(PP, token.getLocation());
			return;
		}

		PP.Lex(token);
		if (!token.isLiteral()) {
			unsupported(PP, token.getLocation());
			return;
		}

		lb = get_int(token.getLiteralData());

		PP.Lex(token);
		if (!token.isLiteral()) {
			unsupported(PP, token.getLocation());
			return;
		}

		ub = get_int(token.getLiteralData());

		dim = isl_dim_set_alloc(ctx, 0, 1);
		set = isl_set_universe(dim);
		set = set_bounds(set, isl_dim_set, 0, lb, ub);

		value_bounds[vd] = set;
	}
};

/* Handle pragmas of the form
 *
 *	#pragma parameter identifier lower_bound upper_bound
 *
 * For each such pragma, intersect the context with the set
 * [identifier] -> { [] : lower_bound <= identifier <= upper_bound }
 */
struct PragmaParameterHandler : public PragmaHandler {
	Sema &sema;
	isl_set *&context;

	PragmaParameterHandler(Sema &sema, isl_set *&context) :
		PragmaHandler("parameter"), sema(sema), context(context) {}

	virtual void HandlePragma(Preprocessor &PP,
				  PragmaIntroducerKind Introducer,
				  Token &ScopTok) {
		isl_id *id;
		isl_ctx *ctx = isl_set_get_ctx(context);
		isl_dim *dim;
		isl_set *set;
		IdentifierInfo *name;
		Decl *decl;
		ValueDecl *vd;
		Token token;
		int lb;
		int ub;

		PP.Lex(token);
		if (token.isNot(tok::identifier)) {
			unsupported(PP, token.getLocation());
			return;
		}

		name = token.getIdentifierInfo();
		decl = sema.LookupSingleName(sema.TUScope, name,
				token.getLocation(), Sema::LookupOrdinaryName);
		vd = decl ? cast_or_null<ValueDecl>(decl) : NULL;
		if (!vd) {
			unsupported(PP, token.getLocation());
			return;
		}

		PP.Lex(token);
		if (!token.isLiteral()) {
			unsupported(PP, token.getLocation());
			return;
		}

		lb = get_int(token.getLiteralData());

		PP.Lex(token);
		if (!token.isLiteral()) {
			unsupported(PP, token.getLocation());
			return;
		}

		ub = get_int(token.getLiteralData());

		id = isl_id_alloc(ctx, vd->getName().str().c_str(), vd);
		dim = isl_dim_set_alloc(ctx, 1, 0);
		dim = isl_dim_set_dim_id(dim, isl_dim_param, 0, id);

		set = isl_set_universe(dim);

		set = set_bounds(set, isl_dim_param, 0, lb, ub);

		context = isl_set_intersect(context, set);
	}
};

/* Handle pragmas of the form
 *
 *	#pragma scop
 *
 * In particular, store the current location in loc.start.
 */
struct PragmaScopHandler : public PragmaHandler {
	ScopLoc &loc;

	PragmaScopHandler(ScopLoc &loc) : PragmaHandler("scop"), loc(loc) {}

	virtual void HandlePragma(Preprocessor &PP,
				  PragmaIntroducerKind Introducer,
				  Token &ScopTok) {
		SourceManager &SM = PP.getSourceManager();
		loc.start = SM.getFileOffset(ScopTok.getLocation());
	}
};

/* Handle pragmas of the form
 *
 *	#pragma endscop
 *
 * In particular, store the current location in loc.end.
 */
struct PragmaEndScopHandler : public PragmaHandler {
	ScopLoc &loc;

	PragmaEndScopHandler(ScopLoc &loc) :
		PragmaHandler("endscop"), loc(loc) {}

	virtual void HandlePragma(Preprocessor &PP,
				  PragmaIntroducerKind Introducer,
				  Token &EndScopTok) {
		SourceManager &SM = PP.getSourceManager();
		loc.end = SM.getFileOffset(EndScopTok.getLocation());
	}
};

/* Extract a pet_scop from the appropriate function.
 * If "function" is not NULL, then we only extract a pet_scop if the
 * name of the function matches.
 * If "autodetect" is false, then we only extract if we have seen
 * scop and endscop pragmas and if these are situated inside the function
 * body.
 */
struct PetASTConsumer : public ASTConsumer {
	Preprocessor &PP;
	ScopLoc &loc;
	const char *function;
	bool autodetect;
	isl_ctx *ctx;
	struct pet_scop *scop;

	PetASTConsumer(isl_ctx *ctx, Preprocessor &PP, ScopLoc &loc,
		const char *function, bool autodetect) :
		ctx(ctx), PP(PP), loc(loc), scop(NULL),
		function(function), autodetect(autodetect) { }

	virtual void HandleTopLevelDecl(DeclGroupRef dg) {
		DeclGroupRef::iterator it;

		if (scop)
			return;
		for (it = dg.begin(); it != dg.end(); ++it) {
			FunctionDecl *fd = dyn_cast<clang::FunctionDecl>(*it);
			if (!fd)
				continue;
			if (!fd->hasBody())
				continue;
			if (function &&
			    fd->getNameInfo().getAsString() != function)
				continue;
			if (autodetect) {
				PetScan ps(ctx, PP, loc, 1);
				scop = ps.scan(fd);
				if (scop)
					break;
				else
					continue;
			}
			if (!loc.end)
				continue;
			SourceManager &SM = PP.getSourceManager();
			if (SM.getFileOffset(fd->getLocStart()) > loc.end)
				continue;
			if (SM.getFileOffset(fd->getLocEnd()) < loc.start)
				continue;
			PetScan ps(ctx, PP, loc, 0);
			scop = ps.scan(fd);
			break;
		}
	}
};

static const char *ResourceDir = CLANG_PREFIX"/lib/clang/"CLANG_VERSION_STRING;

static const char *implicit_functions[] = {
	"min", "max", "ceild", "floord"
};

static bool is_implicit(const IdentifierInfo *ident)
{
	const char *name = ident->getNameStart();
	for (int i = 0; i < ARRAY_SIZE(implicit_functions); ++i)
		if (!strcmp(name, implicit_functions[i]))
			return true;
	return false;
}

/* Ignore implicit function declaration warnings on
 * "min", "max", "ceild" and "floord" as we detect and handle these
 * in PetScan.
 */
struct MyDiagnosticPrinter : public TextDiagnosticPrinter {
	MyDiagnosticPrinter(const DiagnosticOptions &DO) :
		TextDiagnosticPrinter(llvm::errs(), DO) {}
	virtual void HandleDiagnostic(Diagnostic::Level level,
					const DiagnosticInfo &info) {
		if (info.getID() == diag::ext_implicit_function_decl &&
		    info.getNumArgs() == 1 &&
		    info.getArgKind(0) == Diagnostic::ak_identifierinfo &&
		    is_implicit(info.getArgIdentifier(0)))
			/* ignore warning */;
		else
			TextDiagnosticPrinter::HandleDiagnostic(level, info);
	}
};

/* Extract a pet_scop from the C source file called "filename".
 * If "function" is not NULL, extract the pet_scop from the function
 * with that name.
 * If "autodetect" is set, extract any pet_scop we can find.
 * Otherwise, extract the pet_scop from the region delimited
 * by "scop" and "endscop" pragmas.
 *
 * We first set up the clang parser and then try to extract the
 * pet_scop from the appropriate function in PetASTConsumer.
 * If we have found a pet_scop, we add the context and value_bounds
 * constraints specified through pragmas.
 */
struct pet_scop *pet_scop_extract_from_C_source(isl_ctx *ctx,
	const char *filename, const char *function, int autodetect)
{
	isl_dim *dim;
	isl_set *context;
	map<ValueDecl *, isl_set *> value_bounds;
	map<ValueDecl *, isl_set *>::iterator vb_it;

	FileSystemOptions FO;
	FileManager FM(FO);
	const FileEntry *file = FM.getFile(filename);
	if (!file)
		isl_die(ctx, isl_error_unknown, "unable to open file",
			return NULL);

	llvm::IntrusiveRefCntPtr<DiagnosticIDs> DiagID(new DiagnosticIDs());
	DiagnosticOptions DO;
	Diagnostic Diags(DiagID, new MyDiagnosticPrinter(DO));
	TargetOptions TO;
	TO.Triple = llvm::sys::getHostTriple();
	TargetInfo *target = TargetInfo::CreateTargetInfo(Diags, TO);
	SourceManager SM(Diags, FM);
	HeaderSearch HS(FM);
	LangOptions LO;
	CompilerInvocation::setLangDefaults(LO, IK_C,
					    LangStandard::lang_unspecified);
	Preprocessor PP(Diags, LO, *target, SM, HS);
	HeaderSearchOptions HSO;
	PreprocessorOptions PPO;
	FrontendOptions FEO;
	HSO.ResourceDir = ResourceDir;
	InitializePreprocessor(PP, PPO, HSO, FEO);

	ScopLoc loc;

	if (!autodetect) {
		PP.AddPragmaHandler(new PragmaScopHandler(loc));
		PP.AddPragmaHandler(new PragmaEndScopHandler(loc));
	}

	SM.createMainFileID(file);

	ASTContext ast_context(LO, PP.getSourceManager(),
		*target, PP.getIdentifierTable(), PP.getSelectorTable(),
		PP.getBuiltinInfo(), 0);
	PetASTConsumer consumer(ctx, PP, loc, function, autodetect);
	Sema sema(PP, ast_context, consumer);

	dim = isl_dim_set_alloc(ctx, 0, 0);
	context = isl_set_universe(dim);
	PP.AddPragmaHandler(new PragmaParameterHandler(sema, context));
	PP.AddPragmaHandler(new PragmaValueBoundsHandler(ctx, sema, value_bounds));

	Diags.getClient()->BeginSourceFile(LO, &PP);
	ParseAST(sema);
	Diags.getClient()->EndSourceFile();

	delete target;
	llvm::llvm_shutdown();

	if (consumer.scop)
		consumer.scop->context = isl_set_intersect(context,
						    consumer.scop->context);
	else
		isl_set_free(context);

	if (consumer.scop) {
		for (int i = 0; i < consumer.scop->n_array; ++i) {
			isl_id *id;
			ValueDecl *decl;
			pet_array *array = consumer.scop->arrays[i];

			id = isl_set_get_tuple_id(array->extent);
			decl = (ValueDecl *)isl_id_get_user(id);
			isl_id_free(id);

			vb_it = value_bounds.find(decl);
			if (vb_it != value_bounds.end())
				array->value_bounds = isl_set_copy(vb_it->second);
		}
	}

	for (vb_it = value_bounds.begin(); vb_it != value_bounds.end(); vb_it++)
		isl_set_free(vb_it->second);

	return consumer.scop;
}
