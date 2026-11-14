"""Smallest binary grammar objective through variable-arity dictionary parses."""
from grammar import *
from collections import defaultdict
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_array
import time

w=tuple(axword())
cnt=Counter(w[i:j] for i in range(len(w)) for j in range(i+2,len(w)+1))
words=sorted([s for s,c in cnt.items() if c>1],key=lambda x:(len(x),str(x)))+[w]
wordid={s:i for i,s in enumerate(words)}
N=len(words)
objective=[-1.]*N;integrality=[1]*N;lb=[0.]*N;ub=[1.]*N
lb[-1]=1.
entries=[];clo=[];chi=[];edges=[]
def constraint(items,lo,hi):
    r=len(clo)
    for col,v in items:entries.append((r,col,v))
    clo.append(lo);chi.append(hi)
allwordedges=[]
for a,s in enumerate(words):
    local=[];ins=defaultdict(list);outs=defaultdict(list)
    for i in range(len(s)):
        for j in range(i+1,len(s)+1):
            word=s[i:j];v=wordid.get(word)
            if j==i+1 or (v is not None and v!=a):
                eid=len(objective)
                objective.append(1.);integrality.append(0);lb.append(0.);ub.append(1.)
                local.append((i,j,v,eid));ins[j].append(eid);outs[i].append(eid)
                if j>i+1:constraint([(eid,1),(v,-1)],-np.inf,0.)
    for i in range(len(s)+1):
        row=[(e,1) for e in outs[i]]+[(e,-1) for e in ins[i]]
        if i==0:row.append((a,-1))
        elif i==len(s):row.append((a,1))
        constraint(row,0,0)
    allwordedges.append(local)

from collections import defaultdict
rr,cc,vv=zip(*entries)
mat=coo_array((vv,(np.array(rr,dtype=np.int32),np.array(cc,dtype=np.int32))),shape=(len(clo),len(objective))).tocsc()
print('MILP',N,'dictionary words',len(objective),'variables',mat.shape[0],'constraints',flush=True)
res=milp(np.array(objective),integrality=np.array(integrality),bounds=Bounds(lb,ub),constraints=LinearConstraint(mat,clo,chi),options={'time_limit':600,'disp':True,'mip_rel_gap':0.0001})
print(res,flush=True)
if res.x is not None:
    selected={i for i in range(N) if res.x[i]>0.5}
    productions={}
    for a in sorted(selected):
        s=words[a];dp=[(float('inf'),None)]*(len(s)+1);dp[-1]=(0,[])
        for i in range(len(s)-1,-1,-1):
            for ii,j,v,eid in allwordedges[a]:
                if ii==i and (j==i+1 or v in selected):
                    c=1+dp[j][0]
                    if c<dp[i][0]:dp[i]=(c,[(('word',v) if j>i+1 else ('token',s[i]))]+dp[j][1])
        productions[a]=dp[0][1]
    out={'objective':res.fun,'selected':len(selected),'productions':productions,'root':N-1,'words':words}
    Path('milp_result.json').write_text(json.dumps(out,indent=2))
