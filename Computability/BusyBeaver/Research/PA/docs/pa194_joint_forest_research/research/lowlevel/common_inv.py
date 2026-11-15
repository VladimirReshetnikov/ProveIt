from common import *
iv=json.loads((B/'abstract_regs.json').read_text())['intervals'];iv={int(k):v for k,v in iv.items()};inverse={p:i for i,p in enumerate(r.PHYSICAL)}
oldcs=cs;cs=[]
for c in oldcs:
 i,br,s,t=c
 if i not in iv:continue
 if br is not None:
  lo,hi=iv[i][inverse[br[0]]]
  if (br[1] and lo>0) or (not br[1]and hi==0):continue
 cs.append(c)
original_oracle=r.oracle;original_run=r.run;currsite=None
def invariant_oracle(q,br,x):
 out=original_oracle(q,br,x)
 if out is not None:return out
 _,kind,p=x
 if kind=='mark' and p<9 and q==0 and iv[currsite][inverse[p]][1]==0:return 97,r.PLAIN,False
 return None
def invariant_run(rows,c,*args,**kwargs):
 global currsite
 currsite=c[0]
 return original_run(rows,c,*args,**kwargs)
r.oracle=invariant_oracle;r.run=invariant_run
