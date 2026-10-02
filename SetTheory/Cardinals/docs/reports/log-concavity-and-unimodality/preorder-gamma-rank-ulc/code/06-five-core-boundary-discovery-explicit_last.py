import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
from itertools import combinations
import json,time,sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
import kernel as K
N=14;SH=[1<<(4*i)for i in range(N)];PAR=sum(SH)
def unpack(e):return [(e>>(4*i))&15 for i in range(N)]
def polys(rows,m=4):
 out={k:{}for k in [2,3,4]};features=K.features(rows)
 for z,(k,j,S,J)in enumerate(K.PAIRS):
  if k not in out or not features[z]:continue
  core=sum(SH[i]for i in K.IDX[S])+sum(SH[5+i]for i in K.IDX[J])
  for sinks in combinations(range(10,10+m),k-j):out[k][core+sum(SH[i]for i in sinks)]=1
 return out

def gap(rows,m=4):
 g=polys(rows,m);p=defaultdict(int)
 for e in g[3]:
  for f in g[3]:p[e+f]+=3
 for e in g[2]:
  for f in g[4]:p[e+f]-=8
 return {e:c for e,c in p.items()if c}

def certify(p):
 E=sorted(p);ix={e:i for i,e in enumerate(E)};positive={e for e in E if p[e]>0};negative=[e for e in E if p[e]<0];cols=[];metas=[]
 for g in negative:
  for e in positive:
   f=2*g-e
   if e>=f or f not in positive:continue
   m=e&PAR;a=(e-m)//2;b=(f-m)//2
   for ratio in [F(1),F(2),F(3),F(4),F(1,2),F(1,3),F(1,4)]:
    cols.append({e:ratio*ratio,f:F(1),g:-2*ratio});metas.append([unpack(m),[[unpack(a),str(ratio)],[unpack(b),'-1']]])
 if not cols:return None
 rr=[];cc=[];vv=[]
 for j,col in enumerate(cols):
  for e,c in col.items():rr.append(ix[e]);cc.append(j);vv.append(float(c))
 A=coo_matrix((vv,(rr,cc)),shape=(len(E),len(cols))).tocsc();res=linprog(np.ones(len(cols)),A_ub=A,b_ub=[p[e]for e in E],bounds=(0,None),method='highs')
 if not res.success:return None
 out=[];rem={e:F(c)for e,c in p.items()}
 for x,col,meta in zip(res.x,cols,metas):
  if x<1e-9:continue
  w=F(float(x)).limit_denominator(10000000);out.append([str(w),meta])
  for e,c in col.items():rem[e]-=w*c
 if min(rem.values())<0:return None
 return out
if __name__=='__main__':
 R=Path(__file__).parent;end=int(sys.argv[1])if len(sys.argv)>1 else 150;m=int(sys.argv[2])if len(sys.argv)>2 else 4;outdir=R/f'explicit-{m}-sink-last';outdir.mkdir(exist_ok=True);t=time.time();records=[]
 for i,(code,rows)in enumerate(K.core_list()[:end]):
  p=gap(rows,m);out=[]if not p or min(p.values())>=0 else certify(p);rec={'id':i,'passed':out is not None,'target_terms':len(p),'negative_terms':sum(c<0 for c in p.values())};records.append(rec)
  if out is not None:(outdir/f'certificate_{i}.json').write_text(json.dumps({'rows':rows,'sink_count':m,'target':'3gamma3^2-8gamma2gamma4','terms':out},indent=2))
  print(i,'PASS'if out is not None else'UNRESOLVED','terms',len(p),'negative',rec['negative_terms'],'seconds',round(time.time()-t,2),flush=True)
 (R/f'explicit-{m}-sink-last-status.json').write_text(json.dumps({'records':records,'seconds':time.time()-t},indent=2))
