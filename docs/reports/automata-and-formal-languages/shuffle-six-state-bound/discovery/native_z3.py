import ctypes as C
import ctypes.util

_lib = C.CDLL(ctypes.util.find_library('z3') or 'libz3.so.4')
_lib.Z3_mk_config.restype = C.c_void_p
_lib.Z3_del_config.argtypes = [C.c_void_p]
_lib.Z3_mk_context.argtypes = [C.c_void_p]
_lib.Z3_mk_context.restype = C.c_void_p
_lib.Z3_del_context.argtypes = [C.c_void_p]
_lib.Z3_eval_smtlib2_string.argtypes = [C.c_void_p,C.c_char_p]
_lib.Z3_eval_smtlib2_string.restype = C.c_char_p

def solve(text, query=None):
 c = _lib.Z3_mk_config(); ctx = _lib.Z3_mk_context(c); _lib.Z3_del_config(c)
 try:
  r = _lib.Z3_eval_smtlib2_string(ctx, text.encode())
  result = r.decode()
  if query is not None and result.strip() == "sat":
   result += _lib.Z3_eval_smtlib2_string(ctx, query.encode()).decode()
  return result
 finally: _lib.Z3_del_context(ctx)

if __name__ == '__main__':
 import sys
 print(solve(open(sys.argv[1]).read()) if len(sys.argv)>1 else solve('(declare-const x Int)(assert (> x 1))(check-sat)(get-value (x))'))
