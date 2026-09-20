"""Minimal SMT-LIB interface to the system Z3 shared library (no Python package)."""
from __future__ import annotations
import ctypes
import ctypes.util
class Solver:
    def __init__(self):
        path=ctypes.util.find_library('z3')
        if not path: raise RuntimeError('Z3 shared library not found')
        self.lib=ctypes.CDLL(path)
        self.lib.Z3_mk_config.restype=ctypes.c_void_p
        self.lib.Z3_mk_context.argtypes=[ctypes.c_void_p]
        self.lib.Z3_mk_context.restype=ctypes.c_void_p
        self.lib.Z3_del_config.argtypes=[ctypes.c_void_p]
        self.lib.Z3_del_context.argtypes=[ctypes.c_void_p]
        self.lib.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p]
        self.lib.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
        cfg=self.lib.Z3_mk_config()
        self.ctx=self.lib.Z3_mk_context(cfg)
        self.lib.Z3_del_config(cfg)
    def evaluate(self, text:str)->str:
        return self.lib.Z3_eval_smtlib2_string(self.ctx,text.encode()).decode()
    def close(self):
        if self.ctx:self.lib.Z3_del_context(self.ctx);self.ctx=None
    def __enter__(self):return self
    def __exit__(self,*args):self.close()
if __name__=='__main__':
    with Solver() as s:
        print(s.evaluate('(declare-const x Int)(assert (= x 42))(check-sat)(get-value (x))'))
