def add(a,b): return tuple(x+y for x,y in zip(a,b))
from collections import defaultdict
from fractions import Fraction as F
from itertools import permutations,product
from pathlib import Path
import json,numpy as np,time,sys
import sympy as sym
from scipy.optimize import linprog
from scipy.sparse import coo_matrix,hstack,eye
ROOT=Path(__file__).resolve().parent

def group(blocks,mode):
 n=sum(blocks);start=0;pieces=[]
 for b in blocks:pieces.append(list(permutations(range(start,start+b))));start+=b
 perms=[]
 for pp in product(*pieces):
  pp=sum(pp,());q=pp if mode=='vertex'else pp+tuple(n+a for a in pp);perms.append(q)
  if tuple(blocks)==tuple(reversed(blocks)):
   q=tuple(n-1-a for a in pp)if mode=='vertex'else tuple(2*n-1-a for a in pp)+tuple(n-1-a for a in pp);perms.append(q)
 return sorted(set(perms))
def act(e,p):
 out=[0]*len(e)
 for i,j in enumerate(p):out[j]=e[i]
 return tuple(out)

def certify(p,G,iterations=160):
 for e,c in p.items():assert all(p.get(act(e,g),0)==c for g in G)
 gg=defaultdict(list)
 for e,c in p.items():
  if c:
   m=tuple(a%2 for a in e);a=tuple(x//2 for x in e);gg[m].append(a)
 gg={m:bs for m,bs in gg.items()if len(bs)>1};E=set(p)
 for m,bs in gg.items():
  for a in bs:
   for b in bs:E.add(add(m,add(a,b)))
 orbit={e:min(act(e,g)for g in G)for e in E};representatives=sorted(set(orbit.values()));ix={e:i for i,e in enumerate(representatives)}
 for e in E:ix[e]=ix[orbit[e]]
 v=np.zeros(len(representatives))
 for e,c in p.items():v[ix[e]]+=c
 blocks=[(m,bs,np.array([[ix[add(m,add(a,b))]for b in bs]for a in bs]))for m,bs in gg.items()]
 columns=[];metas=[];seen=set();seen_columns=set()
 for m,bs,I in blocks:
  for i,a in enumerate(bs):
   for j,b in enumerate(bs[:i]):
    middle=add(m,add(a,b))
    if p.get(middle,0)>=0 or p.get(add(m,add(a,a)),0)<=0 or p.get(add(m,add(b,b)),0)<=0:continue
    col=defaultdict(F);col[int(I[i,i])]+=1;col[int(I[j,j])]+=1;col[int(I[i,j])]-=2;col={k:c for k,c in col.items()if c};key=tuple(sorted(col.items()))
    if key in seen_columns:continue
    seen_columns.add(key);columns.append(col);metas.append((m,[(a,F(1)),(b,F(-1))]))
 ar=[];ac=[];av=[]
 for j,col in enumerate(columns):
  for i,c in col.items():ar.append(i);ac.append(j);av.append(float(c))
 A=coo_matrix((av,(ar,ac)),shape=(len(v),len(columns))).tocsc()

 for it in range(iterations):
  res=linprog(np.r_[np.zeros(len(columns)),np.ones(len(v))],A_ub=hstack([A,-eye(len(v))],format='csc'),b_ub=v,bounds=(0,None),method='highs')
  if not res.success:return None
  print('it',it,'objective',res.fun,'columns',len(columns),'rows',len(v),'group',len(G),flush=True)
  if res.fun<1e-8:
   weights=[F(float(a)).limit_denominator(10000000)if a>1e-9 else F(0)for a in res.x[:len(columns)]]
   active=[i for i,w in enumerate(weights)if w]
   residual=v-A@res.x[:len(columns)]
   zero=[i for i,r in enumerate(residual)if r<1e-7]
   try:
    M=sym.Matrix([[sym.Rational(columns[j].get(i,0))for j in active]for i in zero]);rhs=sym.Matrix([int(round(v[i]))for i in zero])
    solution,parameters,free=M.gauss_jordan_solve(rhs,freevar=True)
    solution=solution.subs({t:sym.Rational(weights[active[j]])for t,j in zip(parameters,free)})
    trial=[F(0)]*len(columns)
    for j,a in zip(active,solution):trial[j]=F(a)
    rr=[F(int(round(a)))for a in v]
    for w,col in zip(trial,columns):
     for i,c in col.items():rr[i]-=w*c
    if all(w>=0 for w in trial)and all(a>=0 for a in rr):weights=trial;print('exact active-system reconstruction passed',len(active),len(zero),flush=True)
   except (ValueError,ZeroDivisionError) as error:print('exact active-system reconstruction unavailable',str(error),flush=True)
   rem={e:F(c)for e,c in p.items()};out=[]
   for val,col,meta in zip(weights,columns,metas):
    if val<1e-9:continue
    w=val/len(G);m,ss=meta
    for perm in G:
     newmeta=[list(act(m,perm)),[[list(act(a,perm)),str(z)]for a,z in ss]]
     for a,za in ss:
      for b,zb in ss:
       e=act(add(m,add(a,b)),perm);rem[e]=rem.get(e,F(0))-w*za*zb
     out.append([str(w),newmeta])
   if all(c>=0 for c in rem.values()):return out
   print('rounding min',min(rem.values()),flush=True)
  if it and it%15==0:
   keep=[i for i,a in enumerate(res.x[:len(columns)])if a>1e-9];A=A[:,keep];columns=[columns[i]for i in keep];metas=[metas[i]for i in keep];seen=set()
  new=[];newmeta=[]
  for m,bs,I in blocks:
   M=res.ineqlin.marginals[I];vals,vecs=np.linalg.eigh(M)
   for j,val in enumerate(vals):
    if val<1e-8:continue
    vec=vecs[:,j]/max(abs(vecs[:,j]))
    for den in [1,2,3,4,8,16,100,1000,10000]:
     zz=[F(float(z)).limit_denominator(den)for z in vec];ss=[(a,z)for a,z in zip(bs,zz)if z];key=str((m,ss))
     if key in seen:continue
     poly=defaultdict(F)
     for a,za in ss:
      for b,zb in ss:poly[ix[add(m,add(a,b))]]+=za*zb
     poly={i:c for i,c in poly.items()if c}
     if sum(float(c)*res.ineqlin.marginals[i]for i,c in poly.items())<1e-8:continue
     seen.add(key);new.append(poly);newmeta.append((m,ss))
  if not new:return None
  ar=[];ac=[];av=[]
  for j,col in enumerate(new):
   for i,c in col.items():ar.append(i);ac.append(j);av.append(float(c))
  A=hstack([A,coo_matrix((av,(ar,ac)),shape=(len(v),len(new)))],format='csc');columns+=new;metas+=newmeta
 return None

