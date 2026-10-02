import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import json,time,numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

ROOT=Path(__file__).resolve().parent

def certify(p):
 E=sorted(p);ix={e:i for i,e in enumerate(E)};positive={e for e in E if p[e]>0};negative=[e for e in E if p[e]<0];cols=[];metas=[];seen=set()
 for g in negative:
  for e in positive:
   f=tuple(2*x-y for x,y in zip(g,e))
   if f not in positive or e>=f:continue
   m=tuple(v%2 for v in e);a=tuple((v-w)//2 for v,w in zip(e,m));b=tuple((v-w)//2 for v,w in zip(f,m))
   for ratio in [F(1),F(2),F(3),F(4),F(1,2),F(1,3),F(1,4)]:
    col={e:ratio*ratio,f:F(1),g:-2*ratio};cols.append(col);metas.append([list(m),[[list(a),str(ratio)],[list(b),'-1']]])
 if not cols:return None
 rr=[];cc=[];vv=[]
 for j,col in enumerate(cols):
  for e,c in col.items():rr.append(ix[e]);cc.append(j);vv.append(float(c))
 A=coo_matrix((vv,(rr,cc)),shape=(len(E),len(cols))).tocsc()
 res=linprog(np.ones(len(cols)),A_ub=A,b_ub=[p[e]for e in E],bounds=(0,None),method='highs')
 if not res.success:return None
 out=[];rem={e:F(c)for e,c in p.items()}
 for x,col,meta in zip(res.x,cols,metas):
  if x<1e-9:continue
  w=F(float(x)).limit_denominator(10000000);out.append([str(w),meta])
  for e,c in col.items():rem[e]-=w*c
 if min(rem.values())<0:return None
 return out

