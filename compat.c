#include <string.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

#ifdef _MSC_VER
	char *strndup(const char *s, size_t n) {
		size_t m = strlen(s);
		if (n < m)
			m = n;

		char *result = (char*)malloc(m + 1);
		if (!result)
			return 0;

		result[m] = '\0';
		return (char*)memcpy(result, s, m);
	}
#endif /* _MSC_VER */

#ifdef __cplusplus
}
#endif
