"""Adversarial independent test of capacity DP versus exhaustive subsets."""
import random, itertools, json
from functools import lru_cache

def contact(a,b,p):
    for j in range(max(len(a),len(b))):
        if ((a[j] if j<len(a) else 0)-(b[j] if j<len(b) else 0))%p:return j
    raise ValueError("repeat")

def factorial(indices,W):
    sel=[]; vals=[]; remain=list(indices)
    while remain:
        cost,x=min((sum(W[z][y] for y in sel),z) for z in remain)
        vals.append(cost);sel.append(x);remain.remove(x)
    return vals

def tree(indices,W,parentheight=0):
    if len(indices)==1:return (0,())
    height=min(W[i][j] for i,j in itertools.combinations(indices,2))
    left=set(indices);clusters=[]
    while left:
        x=min(left);cluster={y for y in left if y==x or W[x][y]>height}
        left-=cluster;clusters.append(tuple(sorted(cluster)))
    return (height-parentheight,tuple(tree(C,W,height) for C in clusters))

@lru_cache(None)
def C(node,r,T):
    ell,ch=node
    if not ch:
        return 1 if T<=0 or r>=1 else 0
    threshold=T-r*ell
    # Knapsack with allocation <= r.
    budgets=[0]*(r+1)
    for child in ch:
        budgets=[max(budgets[a]+C(child,b-a,threshold) for a in range(b+1)) for b in range(r+1)]
    return budgets[r]

rng=random.Random(911)
counts={"configurations":0,"states_compared":0,"subsets_enumerated":0,"examples":[]}
for p in (2,3,5):
 for k in range(10):
    L=rng.randrange(2,5); N=rng.randrange(1,min(8,p**L)+1)
    pool=[[0]+[(i//p**j)%p for j in range(L)] for i in range(p**L)]
    B=rng.sample(pool,N)
    W=[[0 if i==j else contact(B[i],B[j],p) for j in range(N)] for i in range(N)]
    node=tree(tuple(range(N)),W)
    subsetdata=[]
    for m in range(N+1):
        for sub in itertools.combinations(range(N),m):
            subsetdata.append((m,factorial(sub,W)))
    counts["subsets_enumerated"]+=len(subsetdata)
    maxT=max(factorial(tuple(range(N)),W),default=0)+5
    for r in range(N+1):
        for T in range(0,maxT+1):
            brute=max(m for m,nu in subsetdata if m<=r or nu[r]>=T)
            actual=C(node,r,T)
            assert brute==actual,(p,B,r,T,brute,actual,node)
            counts["states_compared"]+=1
    counts["configurations"]+=1
print(json.dumps(counts,indent=2))

