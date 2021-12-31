#include <caml/mlvalues.h>

value bsmlimpl_init(value arguments);
value bsmlimpl_finalize(value unit);
value bsmlimpl_pid(value unit);
value bsmlimpl_nprocs(value unit);
value bsmlimpl_send(value messages);
value bsmlimpl_at(value condition, value process);
value bsmlimpl_wtime(value unit);
value bsmlimpl_abort(value errorcode);



