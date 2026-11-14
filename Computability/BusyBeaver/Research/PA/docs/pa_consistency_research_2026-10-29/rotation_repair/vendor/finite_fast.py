import ctypes
from pathlib import Path
lib=ctypes.CDLL(str(Path(__file__).with_name('lib_finite_fast.so')));lib.check.argtypes=[ctypes.POINTER(ctypes.c_int),ctypes.c_char_p,ctypes.c_int,ctypes.c_int,ctypes.POINTER(ctypes.c_longlong)];lib.check.restype=ctypes.c_int

def check(t,rows,max_cases=0,variants=1):
 buf=(ctypes.c_int*6000)()
 for (q,b),(w,d,z) in t.items():buf[6*q+3*b]=w;buf[6*q+3*b+1]=d;buf[6*q+3*b+2]=z
 text='\n'.join(f'{p} {op} {arg if arg is not None else 0}' for p,op,arg in rows).encode();steps=ctypes.c_longlong(0)
 return lib.check(buf,text,max_cases,variants,ctypes.byref(steps)),steps.value
if __name__=='__main__':
 from rotation_search import *
 t=read(SRC/'machine/u208.native.tm');rows=json.loads((SRC/'machine/sites.json').read_text());start=time.time();print(check(t,rows,variants=3),time.time()-start)
