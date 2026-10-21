#!/usr/bin/env python3
"""Independent finite named-syntax semantics. No decoder or imported code is executed."""
from pathlib import Path
from itertools import product
import json,sys
if not __debug__ or sys.flags.optimize:raise SystemExit('Assertions must be enabled')
D=Path(__file__).resolve().parent

def rel(i,j):return ('r',i,j)
def eq(i,j):return ('e',i,j)
bot=('b',)
def imp(f,g):return ('i',f,g)
def al(i,f):return ('a',i,f)
def neg(f):return imp(f,bot)
def req(b,k,m):return al(b,imp(m,neg(al(b,imp(m,neg(rel(b,k)))))))
def clos(a,b,k,m):return al(b,imp(rel(b,k),neg(al(a,imp(m,neg(al(a,imp(al(k,imp(rel(k,a),rel(k,b))),req(b,k,m)))))))))
def bundle(a,b,k,m):return neg(imp(imp(rel(a,b),al(k,rel(a,b))),al(k,imp(clos(a,b,k,m),neg(req(b,k,m))))))
def update(e,i,x):return {**e,i:x}
def free(f):
 if f[0] in 're':return {f[1],f[2]}
 if f[0]=='b':return set()
 if f[0]=='i':return free(f[1])|free(f[2])
 return free(f[2])-{f[1]}
def occurs(f):
 if f[0] in 're':return {f[1],f[2]}
 if f[0]=='b':return set()
 if f[0]=='i':return occurs(f[1])|occurs(f[2])
 return occurs(f[2])|{f[1]}
def enc(f):
 def P(x,y):return (x+y)*(x+y+1)//2+y
 if f[0]=='r':return 4*P(f[1],f[2])+1
 if f[0]=='e':return 4*P(f[1],f[2])+3
 if f[0]=='b':return 1
 if f[0]=='i':return 4*P(enc(f[1]),enc(f[2]))
 return 4*P(f[1],enc(f[2]))+2

def sat(f,e,mem,dom):
 if f[0]=='r':return (e.get(f[1],0),e.get(f[2],0)) in mem
 if f[0]=='e':return e.get(f[1],0)==e.get(f[2],0)
 if f[0]=='b':return False
 if f[0]=='i':return not sat(f[1],e,mem,dom) or sat(f[2],e,mem,dom)
 return all(sat(f[2],update(e,f[1],x),mem,dom) for x in dom)

def seed(mem,R,A,dom):
 return any(all(not R(A,y) or any(R(A,z) and (z,C) in mem for z in dom) for y in dom)
  and all((y,C) not in mem or any(R(x,y) and all(
    not all((w,xp) not in mem or (w,y) in mem for w in dom)
    or all(not R(xp,yp) or any(R(xp,z) and (z,C) in mem for z in dom) for yp in dom)
    for xp in dom) for x in dom) for y in dom) for C in dom)

def main():
 atoms=[bot]+[ctor(i,j) for ctor in [rel,eq] for i,j in product(range(3),repeat=2)]
 fs=atoms+[al(i,f) for i in range(3) for f in atoms]+[neg(f) for f in atoms]+[imp(f,g) for f in atoms for g in [rel(0,1),bot]]
 fs=list(dict.fromkeys(fs));named=padding=reflexive=0;counter={}
 for f in fs:
  assert all(i<enc(f) for i in occurs(f))
  assert enc(al(enc(f),f))>1
 for n in [1,2]:
  dom=tuple(range(n));pairs=list(product(dom,repeat=2))
  for mask in range(1<<len(pairs)):
   mem={p for i,p in enumerate(pairs) if mask>>i&1}
   for vals in product(dom,repeat=3):
    e=dict(enumerate(vals))
    for f in fs:
     old=sat(f,e,mem,dom);new=sat(al(enc(f),f),e,mem,dom)
     assert old==new;padding+=1
     if 2 not in free(f):
      R=lambda x,y:sat(f,update(update(e,0,x),1,y),mem,dom)
      assert sat(bundle(0,1,2,f),e,mem,dom)==seed(mem,R,e[0],dom),(n,mem,e,f)
      named+=1;reflexive+=any((x,x) in mem for x in dom)
     elif 'freshness' not in counter:
      R=lambda x,y:sat(f,update(update(e,0,x),1,y),mem,dom)
      b=sat(bundle(0,1,2,f),e,mem,dom);s=seed(mem,R,e[0],dom)
      if b!=s:counter['freshness']={'domain':n,'mem':sorted(mem),'valuation':e,'matrix':f,'bundle':b,'seed':s}
     if 'distinct_roles' not in counter and 2 not in free(f):
      R=lambda x,y:sat(f,update(update(e,0,x),0,y),mem,dom)
      b=sat(bundle(0,0,2,f),e,mem,dom);s=seed(mem,R,e[0],dom)
      if b!=s:counter['distinct_roles']={'domain':n,'mem':sorted(mem),'valuation':e,'matrix':f,'bundle':b,'seed':s}
 assert 'freshness' in counter
 out={'status':'PASS_FINITE_CORROBORATION_NOT_KERNEL_PROOF','sampled_named_formulas':len(fs),'padding_model_valuation_checks':padding,'fresh_named_bundle_equivalence_checks':named,'checks_with_reflexive_membership':reflexive,'missing_hypothesis_counterexamples':counter,'empty_domain_note':'No valuation Nat→empty exists; the theorem retains explicit e.'}
 (D/'named_kernel_result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
