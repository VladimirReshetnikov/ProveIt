import random, math
from collections import deque

def check(n, delta, F):
    p=math.lcm(*range(1,n+1)); t=4*n*n+2
    Ps=[]; X={0}
    Rs=[]; Y=set(F)
    for k in range(t+2*p):
        Ps.append(X); Rs.append(Y)
        X={delta[q][c] for q in X for c in range(2)}
        Y={q for q in range(n) if any(delta[q][c] in Y for c in range(2))}
    P=[Ps[t+(a-t)%p] for a in range(p)]
    R=[Rs[t+(a-t)%p] for a in range(p)]
    reach=[]
    for q in range(n):
        V={q}; todo=[q]
        for u in todo:
            for v in delta[u]:
                if v not in V: V.add(v); todo.append(v)
        reach.append(V)
    unseen=set(range(n)); SCC=[]
    while unseen:
        q=next(iter(unseen)); H={v for v in unseen if v in reach[q] and q in reach[v]}; unseen-=H
        if len(H)==1 and q not in delta[q]: continue
        dist={q:0}; todo=[q]
        for u in todo:
            for v in delta[u]:
                if v in H and v not in dist: dist[v]=dist[u]+1; todo.append(v)
        d=0
        for u in H:
            for v in delta[u]:
                if v in H: d=math.gcd(d,dist[u]+1-dist[v])
        SCC.append((H,q,dist,d))
    for r in range(p):
        if not P[r]&F: continue
        S=[P[a]&R[(r-a)%p] for a in range(p)]
        C=[{c for c in range(2) if any(delta[q][c] in S[(a+1)%p] for q in S[a])} for a in range(p)]
        U={(a,q) for a in range(p) for q in S[a]}
        while True:
            V={(a,q) for a,q in U if all(((a+1)%p,delta[q][c]) in U for c in C[a])}
            if V==U: break
            U=V
        stripes=False
        for H,q0,dist,d in SCC:
            for h in range(d):
                if q0 not in S[h]: continue
                W={(a,q) for a in range(p) for q in H if (a-dist[q]-h)%d==0}
                assert all(q in S[a] for a,q in W), ('viability',n,delta,F,r,H,h)
                if all(delta[q][c] in H for a,q in W for c in C[a]): stripes=True
        assert bool(U)==stripes, ('equiv',n,delta,F,r,U,SCC)

random.seed(153735)
count=0
for n in range(1,9):
    for j in range(300 if n<6 else (15 if n==6 else 2)):
        delta=[[random.randrange(n) for c in range(2)] for q in range(n)]
        F={q for q in range(n) if random.randrange(2)}
        check(n,delta,F); count+=1
print('Passed',count,'random complete binary DFAs, 1–8 states; all live residues tested.')
