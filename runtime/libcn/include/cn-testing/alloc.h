#ifndef CN_GEN_ALLOC_H
#define CN_GEN_ALLOC_H

#include <stdlib.h>

#include <cn-executable/utils.h>

#ifdef __cplusplus
extern "C" {
#endif

    void cn_gen_alloc_reset(void);

    cn_pointer* cn_gen_alloc(cn_bits_u64* sz);

    cn_bits_u64* cn_gen_alloc_size(cn_pointer* p);

#ifdef __cplusplus
}
#endif

#endif // CN_GEN_ALLOC_H