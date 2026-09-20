"""Optional Z3 search engine used to discover the bundled certificates.

No part of the independent verification imports this module.  Requires a Z3
shared library, located automatically or with the Z3_LIBRARY environment variable.
The numerical witnesses, not the solver status or internal proof trace, are checked.
"""
import ctypes, ctypes.util, re, os
library_path = os.environ.get('Z3_LIBRARY') or ctypes.util.find_library('z3')
if not library_path:
    raise RuntimeError('Z3 shared library not found; set Z3_LIBRARY to its path')
lib = ctypes.CDLL(library_path)
def fn(name,restype,args):
 f=getattr(lib,name);f.restype=restype;f.argtypes=args;return f
p=ctypes.c_void_p;s=ctypes.c_char_p
mkconfig=fn('Z3_mk_config',p,[])
delconfig=fn('Z3_del_config',None,[p])
mkcontext=fn('Z3_mk_context',p,[p])
delcontext=fn('Z3_del_context',None,[p])
evalz3=fn('Z3_eval_smtlib2_string',s,[p,s])
def solve(script,timeout=10000):
 cfg=mkconfig();ctx=mkcontext(cfg);delconfig(cfg)
 parts=script.split('(get-value',1)
 out=evalz3(ctx,(f'(set-option :timeout {timeout})\n'+parts[0]).encode()).decode()
 if out.strip()=='sat' and len(parts)==2:
  out+=evalz3(ctx,('(get-value'+parts[1]).encode()).decode()
 delcontext(ctx)
 return out
if __name__=='__main__':
 print(solve('(declare-const x Int) (assert (> x 2)) (check-sat) (get-value (x))'))
def pred_smt(S,m,n,smaller=True,permutation=False,exclude_same=False,spanning=False):
 S=set(S);o=[]
 def emit(x):o.append(x)
 def AND(xs): return '(and '+' '.join(xs)+')' if xs else 'true'
 def OR(xs): return '(or '+' '.join(xs)+')' if xs else 'false'
 for i in range(m):emit(f'(declare-const f{i} Int) (assert (and (<= 0 f{i}) (< f{i} {m})))')
 for j in range(n):emit(f'(declare-const g{j} Int) (assert (and (<= 0 g{j}) (< g{j} {n})))')
 names=[]
 for i in range(m):
  for j in range(n):
   t=f't{i}_{j}';names.append(t);emit(f'(declare-const {t} Bool)')
   emit(f'(assert (=> {t} {AND([OR([f"(= f{i} {r})" for r in range(m) if (r,j) in S]),OR([f"(= g{j} {c})" for c in range(n) if (i,c) in S])])}))')
 for r,c in sorted(S):
  emit('(assert '+OR([f'(and t{i}_{c} (= f{i} {r}))' for i in range(m)]+[f'(and t{r}_{j} (= g{j} {c}))' for j in range(n)])+')')
 emit('(assert '+OR([f't0_{j}' for j in range(n)])+')')
 emit('(assert '+OR([f't{i}_0' for i in range(m)])+')')
 if spanning:
  for i in range(m):emit('(assert '+OR([f't{i}_{j}' for j in range(n)])+')')
  for j in range(n):emit('(assert '+OR([f't{i}_{j}' for i in range(m)])+')')
 if smaller:emit('(assert (< (+ '+' '.join(f'(ite {t} 1 0)' for t in names)+f') {len(S)}))')
 if permutation:
  emit('(assert (distinct '+' '.join(f'f{i}' for i in range(m))+'))')
  emit('(assert (distinct '+' '.join(f'g{j}' for j in range(n))+'))')
 if exclude_same:emit('(assert '+OR([f'(not t{i}_{j})' if (i,j) in S else f't{i}_{j}' for i in range(m) for j in range(n)])+')')
 emit('(check-sat)')
 emit('(get-value ('+' '.join([f'f{i}' for i in range(m)]+[f'g{j}' for j in range(n)]+names)+'))')
 return '\n'.join(o)
def getpred(S,m,n,timeout=10000,**kw):
 out=solve(pred_smt(S,m,n,**kw),timeout)
 if out.startswith('sat'):
  vals=dict(re.findall(r'\(([fg]\d+|t\d+_\d+) (\d+|true|false)\)',out))
  f=[int(vals[f'f{i}']) for i in range(m)];g=[int(vals[f'g{j}']) for j in range(n)]
  T={(i,j) for i in range(m) for j in range(n) if vals[f't{i}_{j}']=='true'}
  image={(f[i],j) for i,j in T}|{(i,g[j]) for i,j in T}
  assert image==set(S),(image,S)
  assert any(i==0 for i,j in T) and any(j==0 for i,j in T)
  if kw.get('smaller',True):assert len(T)<len(S)
  return {'status':'sat','f':f,'g':g,'T':sorted(T)}
 return {'status':out.splitlines()[0]}
