#!/usr/bin/env python3
"""Equivalent vacuity and contrapositive head variants; h1 is retained."""
import word_variants as v
from fused_gate_variants import repair
import itertools,json,time,collections,sys
OUT=v.BASE/'work/logic/vacuity_variants';OUT.mkdir(exist_ok=True)
def vac(atom,c,mode):
 if mode==0:return v.I(atom,v.U(c,atom))
 if mode==1:return v.I(v.N(atom),v.U(c,v.N(atom)))
 return v.I(v.N(v.U(c,atom)),v.N(atom))
def gate(dm,vm,swap,flip):
 a,b,c='HDA'
 delta=vac(v.E(a,b,flip),c,dm);vv=vac(v.M(a,b),c,vm)
 p=v.I(c,v.M(c,b));s=v.U(b,v.And(v.I(v.M(a,b),p),v.I(v.M(c,b),c)))
 q=v.U(c,v.I(s,v.N(p)))
 return v.N(v.I(vv,v.I(delta,q)))if swap else v.N(v.I(delta,v.I(vv,q)))

start=time.monotonic();best=999;effbest=62;hist=collections.Counter();count=0
for mf,ef,dm,vm,swap,flags in itertools.product((False,True),(False,True),range(3),range(3),(False,True),range(8)):
 v.M=(lambda a,b:v.C(1,b,a))if mf else(lambda a,b:v.C(1,a,b))
 hw=list(map(v.emit,v.heads(flags,ef)));g=v.emit(gate(dm,vm,swap,ef))
 # First screen all logical choices with original order and a few plausible
 # orders; the head permutation corpus already covers 720 orders separately.
 for order in [(0,1,2,3,4,5),(4,0,1,2,3,5),(0,4,1,2,3,5),(0,1,4,2,3,5),(0,1,2,4,3,5),(0,1,2,3,5,4),(5,0,1,2,3,4)]:
  w=v.prefix+sum((hw[j]for j in order),[])+g+v.suffix
  meta={'Mflip':mf,'Eflip':ef,'eq_vacuity_mode':dm,'mem_vacuity_mode':vm,'gate_swap':swap,'flags':flags,'order':order}
  n,t=repair(w);hist[n]+=1;count+=1
  if n<best:
   best=n;print('BEST',n,'len',len(w),meta,'seconds',time.monotonic()-start,flush=True)
   (OUT/f'best_{n}.grammar.json').write_text(json.dumps(v.encode(t),indent=2))
   (OUT/f'best_{n}.meta.json').write_text(json.dumps({'meta':meta,'word':w},indent=2))
  if n<=70:
   r,idx,sh=v.build(t);ops=v.opportunities_fast(r,sh);matching=v.max_matching(ops);eff=n-len(matching)
   if eff<effbest:
    effbest=eff;print('EFFECTIVE',eff,n,meta,flush=True)
    (OUT/f'effective_{eff}.grammar.json').write_text(json.dumps(v.encode(t),indent=2))
    (OUT/f'effective_{eff}.meta.json').write_text(json.dumps({'meta':meta,'word':w,'matching':matching},indent=2))
(OUT/'results.json').write_text(json.dumps({'count':count,'DAGbest':best,'effectivebest':effbest,'hist':hist},indent=2))
print('DONE',count,best,effbest,'seconds',time.monotonic()-start,flush=True)
