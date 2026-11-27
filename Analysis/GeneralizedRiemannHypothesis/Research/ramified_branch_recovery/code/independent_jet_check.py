"""Independent finite-field checks of the proposed total-jet recovery cutoff.
Does not import theorem implementation or use Smith/Weierstrass routines.
Observations are expanded directly as finite polynomials and exact row spaces.
"""
from itertools import combinations, permutations
import random, json

def mul(a,b,p,n):
    c=[0]*n
    for i,ai in enumerate(a[:n]):
        if ai:
            for j,bj in enumerate(b[:n-i]):
                c[i+j]=(c[i+j]+ai*bj)%p
    return c

def valdiff(a,b,p):
    for i in range(max(len(a),len(b))):
        if ((a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0))%p:
            return i
    raise ValueError("not distinct")

def greedy(B,p):
    selected=[]
    costs=[]
    todo=list(range(len(B)))
    while todo:
        c,i=min((sum(valdiff(B[z],B[y],p) for y in selected),z) for z in todo)
        costs.append(c); selected.append(i); todo.remove(i)
    return costs,selected

def rank_mod(rows,p):
    rows=[[(x%p) for x in r] for r in rows]
    if not rows:return 0
    rank=0
    for col in range(len(rows[0])):
        at=next((i for i in range(rank,len(rows)) if rows[i][col]),None)
        if at is None: continue
        rows[rank],rows[at]=rows[at],rows[rank]
        iv=pow(rows[rank][col],-1,p)
        rows[rank]=[(iv*x)%p for x in rows[rank]]
        for i in range(rank+1,len(rows)):
            a=rows[i][col]
            if a:
                rows[i]=[(x-a*y)%p for x,y in zip(rows[i],rows[rank])]
        rank+=1
        if rank==len(rows):break
    return rank

def jet_ambiguity(B,p,d,n):
    # Coefficients of total degree >=n do not affect an observation modulo X^n.
    # Include total degree <d as well when n<d.
    m=max(n,d)
    mons=[(a,b) for b in range(m) for a in range(m-b)]
    rows=[]
    for u in B:
        powers=[[1]+[0]*max(0,n-1)] if n else [[]]
        for b in range(1,m): powers.append(mul(powers[-1],u,p,n))
        for k in range(n):
            rows.append([powers[b][k-a] if 0<=k-a<n else 0 for a,b in mons])
    jetrows=[]
    for j,(a,b) in enumerate(mons):
        if a+b<d:
            row=[0]*len(mons);row[j]=1;jetrows.append(row)
    r=rank_mod(rows,p)
    return rank_mod(rows+jetrows,p)-r

rng=random.Random(20261126)
summary={"fixed_examples":[],"random_checks":0,"tie_checks":0}
examples=[
 (2,[[0],[0,1]],2),
 (2,[[0],[0,0,1],[0,1],[0,1,0,0,1]],3),
 (3,[[0],[0,1],[0,2],[0,0,0,1],[0,1,1]],4),
 (2,[[0],[0,0,0,1],[0,0,1],[0,0,1,0,1],[0,1]],4),
]
for p,B,d in examples:
    nu,_=greedy(B,p); n=nu[d-1]+1
    assert jet_ambiguity(B,p,d,n)==0
    below=jet_ambiguity(B,p,d,n-1)
    assert below>0
    summary["fixed_examples"].append({"p":p,"B":B,"d":d,"nu":nu,"cutoff":n,"ambiguity_dimension_at_cutoff_minus_1":below})
for p in (2,3,5):
    for z in range(25):
        length=rng.randrange(2,5)
        universe=[[0]+[(i//(p**j))%p for j in range(length)] for i in range(p**length)]
        N=rng.randrange(1,min(6,len(universe))+1)
        B=rng.sample(universe,N)
        d=rng.randrange(1,N+1)
        nu,_=greedy(B,p)
        assert all(nu[i+1]>=nu[i]+1 for i in range(N-1))
        n=nu[d-1]+1
        assert jet_ambiguity(B,p,d,n)==0, (p,B,d,n)
        assert jet_ambiguity(B,p,d,n-1)>0,(p,B,d,n)
        if N<=5:
            # Independently recurse over all tied greedy choices.
            observed=set()
            def visit(sel,left,costs):
                if not left: observed.add(tuple(costs));return
                vals=[(sum(valdiff(B[i],B[j],p) for j in sel),i) for i in left]
                minimum=min(v for v,_ in vals)
                for v,i in vals:
                    if v==minimum:
                        visit(sel+[i],[x for x in left if x!=i],costs+[v])
            visit([],list(range(N)),[])
            assert observed=={tuple(nu)}
            summary["tie_checks"]+=1
        summary["random_checks"]+=1
print(json.dumps(summary,indent=2))

