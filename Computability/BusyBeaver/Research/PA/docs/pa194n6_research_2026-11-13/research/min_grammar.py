"""MILP for a macro-word grammar's summed RHS binary costs.

The selected repeated-substring dictionary is finite and word preserving.
This optimizer alone says nothing about valid TM scanner bounds or folding.
"""
from pathlib import Path
import json, collections, time
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix

HERE=Path(__file__).resolve().parent
P=HERE/'inputs/primary.grammar.json'
d=json.loads(P.read_text());rules=d['rules'];inc=('leaf','inc',1)
def word(x):
    if isinstance(x,list):return (tuple(x),)
    if x=='node60':return (inc,)*2
    if x=='node61':return (inc,)*4
    if x in rules:return word(rules[x][0])+word(rules[x][1])
    return (x,)
w=word(d['root'])
counts=collections.Counter(w[i:j] for i in range(len(w))for j in range(i+2,len(w)+1))
free={(inc,)*2:'node60',(inc,)*4:'node61'}
subs=sorted((x for x,n in counts.items()if n>1 and x not in free),key=lambda x:(len(x),repr(x)))+[w]
idx={s:i for i,s in enumerate(subs)}
nv=len(subs);obj=[-1.]*nv;lo=[0.]*nv;hi=[1.]*nv;lo[-1]=1
edges=[];cr=[];cc=[];cv=[];bl=[];bu=[]
def constraint(items,l,u):
    r=len(bl)
    for j,v in items:cr.append(r);cc.append(j);cv.append(v)
    bl.append(l);bu.append(u)
for k,s in enumerate(subs):
    outgoing=collections.defaultdict(list);incoming=collections.defaultdict(list)
    for i in range(len(s)):
        for j in range(i+1,len(s)+1):
            t=s[i:j]
            if len(t)>1 and(t not in free and(t not in idx or len(t)>=len(s))):continue
            e=len(obj);obj.append(1.);lo.append(0.);hi.append(1.)
            edges.append((e,k,i,j,t));outgoing[i].append(e);incoming[j].append(e)
            if t in idx:constraint([(e,1),(idx[t],-1)],-np.inf,0.)
    for i in range(len(s)+1):
        v=[(e,1)for e in outgoing[i]]+[(e,-1)for e in incoming[i]]
        if i==0:v.append((k,-1))
        if i==len(s):v.append((k,1))
        constraint(v,0.,0.)
A=coo_matrix((cv,(cr,cc)),shape=(len(bl),len(obj))).tocsc()
print('problem',len(w),'substrings',nv,'variables',len(obj),'rows',len(bl),flush=True)
start=time.monotonic()
r=milp(np.array(obj),integrality=np.ones(len(obj)),bounds=Bounds(lo,hi),constraints=LinearConstraint(A,bl,bu),options={'time_limit':180.,'mip_rel_gap':0.,'disp':True})
print('RESULT',r,flush=True)
if r.x is None:raise SystemExit('no feasible grammar')
chosen={k:[]for k in range(nv)if r.x[k]>.5}
for e,k,i,j,t in edges:
    if r.x[e]>.5:chosen[k].append((i,j,t))
for k,es in chosen.items():
    es.sort()
    assert tuple(x for _,_,t in es for x in t)==subs[k]

def leaf(t):
    if len(t)==1:return t[0]
    if t in free:return free[t]
    return 's'+str(idx[t])
data={'objective':float(r.fun),'bound':float(r.mip_dual_bound),'gap':float(r.mip_gap),'elapsed':time.monotonic()-start,'root':'s'+str(nv-1),'productions':{'s'+str(k):[leaf(t)for i,j,t in es]for k,es in chosen.items()}}
(HERE/'min_grammar_result.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({k:v for k,v in data.items()if k!='productions'},indent=2))
