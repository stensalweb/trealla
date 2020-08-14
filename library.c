#include "library.h"

extern uint8_t _binary_library_lists_pro_start[];
extern uint8_t _binary_library_lists_pro_end[];

extern uint8_t _binary_library_dict_pro_start[];
extern uint8_t _binary_library_dict_pro_end[];

extern uint8_t _binary_library_apply_pro_start[];
extern uint8_t _binary_library_apply_pro_end[];

extern uint8_t _binary_library_http_pro_start[];
extern uint8_t _binary_library_http_pro_end[];

library g_libs[] = {
     {"lists", _binary_library_lists_pro_start, _binary_library_lists_pro_end},
     {"dict", _binary_library_dict_pro_start, _binary_library_dict_pro_end},
     {"apply", _binary_library_apply_pro_start, _binary_library_apply_pro_end},
     {"http", _binary_library_http_pro_start, _binary_library_http_pro_end},
     {0}
};
