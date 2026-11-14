from collections import defaultdict
from functools import lru_cache
from pathlib import Path
import json,sys
sys.dont_write_bytecode=True
import source_inventory as I
L=I.L
@lru_cache(None)
def effect(n):
 # Each entry (a,b) denotes a*x+b; a is zero or one.
 if L.leaf(n):
  if n[0]!='CI':return None
  out=[(1,0)]*9;out[n[1]]=(1,1);return tuple(out)
 if L.leaf(n[0])and n[0][0]=='CD'and n[1]==('CC',1):
  out=[(1,0)]*9;out[n[0][1]]=(0,0);return tuple(out)
 a,b=effect(n[0]),effect(n[1])
 if a is None or b is None:return None
 return tuple((aa*ba,ba*ab+bb)for(aa,ab),(ba,bb)in zip(a,b))

def run(cls,t,rows):
 root,occ,_=I.inventory(t,rows);groups=defaultdict(list);recognized=[]
 for q,os in occ.items():
  sigs=set(effect(n)for _,n in os)
  if None in sigs or len(sigs)!=1:continue
  sig=next(iter(sigs));groups[sig].append(q);recognized.append({'state':q,'primitives':len(L.sites(os[0][1])),'effect':sig,'occurrences':len(os)})
 donors=[{'states':qs,'effect':eff}for eff,qs in groups.items()if len(qs)>1]
 print(cls,'recognized',recognized,'donors',donors,flush=True)
 return {'class':cls,'recognized':recognized,'donors':donors}
if __name__=='__main__':
 b=I.base;res=[]
 for cls,tp,sp in [('A',b/'machine/variant_plain/u208.native.tm',b/'machine/variant_plain/u208.sites.json'),('B',b/'machine/u208.native.tm',b/'machine/u208.sites.json')]:res.append(run(cls,I.read(tp),json.loads(sp.read_text())))
 Path('analysis/comparison/affine_donors.json').write_text(json.dumps(res,indent=2)+'\n')
