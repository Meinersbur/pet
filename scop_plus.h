#ifndef PET_SCOP_PLUS_H
#define PET_SCOP_PLUS_H

#include <set>
#include <vector>
#include <clang/AST/Decl.h>

#include "scop.h"

/* Compare two sequences of ValueDecl pointers based on their names.
 */
struct array_desc_less {
	bool operator()(const std::vector<clang::ValueDecl *> &x,
			const std::vector<clang::ValueDecl *> &y) {
		int x_n = x.size();
		int y_n = y.size();

		for (int i = 0; i < x_n && i < y_n; ++i) {
			int cmp = x[i]->getName().compare(y[i]->getName());
			if (cmp)
				return cmp < 0;
		}

		return x_n < y_n;
	}
};

/* A sorted set of sequences of ValueDecl pointers.  The actual order
 * is not important, only that it is consistent across platforms.
 */
typedef std::set<std::vector<clang::ValueDecl *>, array_desc_less>
								array_desc_set;

void pet_scop_collect_arrays(struct pet_scop *scop, array_desc_set &arrays);

#endif
