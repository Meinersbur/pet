#include "gitversion.h"

const char *pet_version(void)
{
	return GIT_HEAD_ID"\n";
}
