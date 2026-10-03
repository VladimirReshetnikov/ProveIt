import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
from collections import defaultdict
from math import factorial
import json,time
import kernel as K
import explicit_last as S
S.N=12
SH=S.SH
E={0:[(0,1)],1:[(SH[10],1),(SH[11],1)],2:[(SH[10]+SH[11],2),(2*SH[11],1)],3:[(SH[10]+2*SH[11],3),(3*SH[11],1)]}
def polynomial(rows):
 feat=K.features(rows);g=[None,{}, {}, {}]
 for z,(k,j,tail,head)in enumerate(K.PAIRS):
  if k>3 or not feat[z]:continue
  ex=sum(SH[i]for i in K.IDX[tail])+sum(SH[5+i]for i in K.IDX[head]);coef=factorial(k)//factorial(k-j)
  for m,c in E[k-j]:g[k][ex+m]=coef*c
 p=defaultdict(int)
 for e,c in g[2].items():
  for f,d in g[2].items():p[e+f]+=2*c*d
 for e,c in g[1].items():
  for f,d in g[3].items():p[e+f]-=3*c*d
 return{e:c for e,c in p.items()if c}
if __name__=='__main__':
 R=Path(__file__).parent;outdir=R/'cubic-nine-fourths';t=time.time();recs=[]
 for i,(code,rows)in enumerate(K.core_list()):
  file=outdir/f'certificate_{i}.json'
  if file.exists():continue
  p=polynomial(rows);out=[]if min(p.values())>=0 else S.certify(p)
  rec={'id':i,'rows':rows,'preorder':K.is_preorder(rows),'passed':out is not None};recs.append(rec)
  if out is not None:file.write_text(json.dumps({'rows':rows,'target':'2G2^2-3G1G3','terms':out},indent=2))
  else:print('UNRESOLVED',i,flush=True)
  if i%100==0:print(i,'passed',sum(r['passed']for r in recs),'unresolved',sum(not r['passed']for r in recs),'seconds',round(time.time()-t,2),flush=True)
 (R/'packed-cubic-status.json').write_text(json.dumps({'records':recs,'seconds':time.time()-t},indent=2));print('DONE',len(recs),sum(r['passed']for r in recs),flush=True)
