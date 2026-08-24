"""Same exact toy lab, but the grid now ALSO contains non-mesoscopic (theta < 7/12) cells,
which the report's admissibility condition excludes and which Theorem A cannot reach.
Full exact integrality test against every prime <= N_max."""
import numpy as np, itertools, sys
from math import log
M,A,n,m = 5,11,3,3
def sieve(X):
    s=bytearray([1])*(X+1); s[0]=s[1]=0
    for i in range(2,int(X**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(X+1) if s[i]]
K=[M**(n+i) for i in range(5)]; N=[A**(m+j) for j in range(3)]
cells=[(i,j) for j in range(3) for i in range(5) if K[i]<=N[j]]
theta={(i,j):((n+i)*log(M))/((m+j)*log(A)) for (i,j) in cells}
short=[c for c in cells if theta[c]<7/12]
print("all cells with K<=N:",cells)
print("theta:",{k:round(v,3) for k,v in theta.items()})
print("NON-mesoscopic (theta<7/12) cells:",short)
P=sieve(max(N))
def vpf(X,p):
    t=0;q=p
    while q<=X: t+=X//q; q*=p
    return t
V=np.zeros((len(P),len(cells)),dtype=np.int64)
for ci,(i,j) in enumerate(cells):
    for pi,p in enumerate(P):
        V[pi,ci]=vpf(N[j],p)-vpf(N[j]-K[i],p)
Vu=np.unique(V,axis=0)
print("primes tested:",len(P),"distinct valuation vectors:",Vu.shape[0])
w=np.array([M**i*A**j for (i,j) in cells],dtype=np.int64)
print("weights:",list(w))
# spanning-tree (unimodular) basis of {c : c.w = 0}
pos={c:k for k,c in enumerate(cells)}
edges=[]
seen={cells[0]}
frontier=[cells[0]]
while frontier:
    u=frontier.pop()
    for v in cells:
        if v in seen: continue
        if (abs(v[0]-u[0]),abs(v[1]-u[1])) in [(1,0),(0,1)]:
            edges.append((u,v)); seen.add(v); frontier.append(v)
assert len(edges)==len(cells)-1, (len(edges),len(cells))
Bas=np.zeros((len(edges),len(cells)),dtype=np.int64)
for r,(u,v) in enumerate(edges):
    rw = w[pos[v]]//w[pos[u]] if w[pos[v]]%w[pos[u]]==0 else None
    if rw is not None:
        Bas[r,pos[u]]=-rw; Bas[r,pos[v]]=1
    else:
        rw2 = w[pos[u]]//w[pos[v]]
        Bas[r,pos[v]]=-rw2; Bas[r,pos[u]]=1
assert np.all(Bas@w==0)
B=int(sys.argv[1]) if len(sys.argv)>1 else 2
coef=np.array(list(itertools.product(range(-B,B+1),repeat=len(edges))),dtype=np.int64)
C=coef@Bas
C=C[np.any(C!=0,axis=1)]
print("nonzero balanced vectors:",C.shape[0],"max|c| =",int(np.abs(C).max()))
found=[];best=-10**9;bc=None
CH=20000
for s in range(0,C.shape[0],CH):
    blk=C[s:s+CH]; val=(blk@Vu.T).min(axis=1)
    for r in np.nonzero(val>=0)[0]: found.append(blk[r].copy())
    r=int(val.argmax())
    if val[r]>best: best=int(val[r]); bc=blk[r].copy()
print("INTEGRAL nonzero balanced patterns:",len(found))
for c in found[:20]: print("   ",{cells[k]:int(c[k]) for k in range(len(cells)) if c[k]})
print("best min_p v_p(F):",best,"at",{cells[k]:int(bc[k]) for k in range(len(cells)) if bc[k]})
