"""Owned exact AST reassociation census; no supplied code is executed.

Prices below use the owned origin-preserving incremental allocator. They are
provisional physical counts, not primitive-interface proofs.
"""
from pathlib import Path
import sys,json,time,signal
from functools import lru_cache
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_encoding'));import price_sources as P
from compose_rho_nop import flatten,subst
sys.path.insert(0,str(ROOT/'k223_merged_runtime_audit/runtime'));import independent_runtime as R
I=('CI',1);old=((I,I),(I,I)),('CC',2)
@lru_cache(None)
def shapes(n):
 if n==1:return (None,)
 return tuple((a,b)for k in range(1,n)for a in shapes(k)for b in shapes(n-k))
def fill(shape):
 count=0
 def f(s,depth):
  nonlocal count
  if s is None:
   count+=1;return I if count<5 else ('CC',depth+1)
  return f(s[0],depth+1),f(s[1],depth+1)
 return f(shape,0)
def cfg(sites):
 leaves={p:i for i,(p,op,arg)in enumerate(sites)}
 def dest(p):
  for unused in range(100):
   for k in range(len(p)+1):
    if p[:k] in leaves:
     assert set(p[k:])<= {'0'},('noncanonical remaining bits',p,k)
     return leaves[p[:k]]
   p+='0'
  raise AssertionError(('noncode',p))
 result=[]
 for p,op,arg in sites:
  if op=='CH':edges=[]
  elif op=='CC':edges=[dest(R.strip(p,'1',arg))]
  elif op=='CB':edges=[dest(R.inc(R.strip(p,'0',arg))[0])]
  elif op=='CD':edges=[dest(R.inc(R.strip(p,'0',1))[0]),dest(R.inc(p)[0])]
  else:edges=[dest(R.inc(p)[0])]
  result.append([op,None if op in('CC','CB')else arg,edges])
 return result
def main():
 t0=time.monotonic();B=ROOT/'latest219_baseline/candidate-k219';T=P.D.table(B/'k219.native.tm');sites=json.load(open(B/'sites219.json'));src=P.tree(sites);reference=cfg(sites)
 realallocation=P.allocation;cached=realallocation(T,src)
 # Avoid repeating the exact unchanged baseline prefix walk. Suppress the
 # candidate prefix pass only during provisional pricing, marked explicitly.
 def cached_allocation(table,tree):
  if table==T and tree==src:return cached
  return {},{},[]
 P.allocation=cached_allocation;reports=[]
 signal.signal(signal.SIGALRM,lambda*a:(_ for _ in()).throw(TimeoutError('2-second census cap')));signal.alarm(2)
 try:
  for i,shape in enumerate(shapes(5)):
   tree=fill(shape);new,n=subst(src,old,tree);assert n==81
   ns=flatten(new);assert cfg(ns)==reference
   rec=dict(index=i,macro=tree,occurrences=n,leaves=len(ns),distinct_subtrees=len(P.nodes(new))+len({(op,arg)for p,op,arg in ns}),internal_subtrees=len(P.nodes(new)),depth=max(len(p)for p,op,arg in ns),exact_ordinal_cfg=True)
   try:
    U,price=P.compile(T,src,new);rec.update(price);rec['binding_failures']='NOT_CHECKED_DURING_PROVISIONAL_PRICING'
    d=OUT/f'four_increment_{i:02d}';d.mkdir(exist_ok=True);(d/'sites.json').write_text(json.dumps(ns,indent=2)+'\n');(d/'native.tm').write_bytes(P.M.enc(U))
    if len(U)<438 or price['removed']:
     g,p,_=realallocation(U,new);rec['prefix_binding_checked']=True;rec['decoder_states']=len(g)
   except Exception as e:rec['price_error']=repr(e)
   reports.append(rec)
 except TimeoutError as e:reports.append({'status':'CAP_UNKNOWN','error':str(e)})
 finally:
  signal.alarm(0);P.allocation=realallocation
  out=dict(reports=reports,seconds=time.monotonic()-t0,scope='Exact AST, occurrence count, and ordinal CFG. Physical prices provisional; no all-natural arithmetic or startup proof.')
  (OUT/'FOUR_INCREMENT_REASSOCIATIONS.json').write_text(json.dumps(out,indent=2)+'\n')
  print(json.dumps({**{k:v for k,v in out.items()if k!='reports'},'reports':[{k:v for k,v in r.items()if k in('index','states','distinct_subtrees','internal_subtrees','added','removed','price_error','status','exact_ordinal_cfg')}for r in reports]}))
if __name__=='__main__':main()
