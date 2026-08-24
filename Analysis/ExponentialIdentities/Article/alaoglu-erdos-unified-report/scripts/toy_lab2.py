"""Second independent exact laboratory: M=7, A=19 (multiplicatively independent, generic)."""
import numpy as np, itertools
from math import log
M,A,n,m=7,19,3,3
def sieve(X):
    s=bytearray([1])*(X+1); s[0]=s[1]=0
    for i in range(2,int(X**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(X+1) if s[i]]
K=[M**(n+i) for i in range(5)]; N=[A**(m+j) for j in range(3)]
cells=[(i,j) for j in range(3) for i in range(5) if K[i]<=N[j]//2 and K[i]>=N[j]**(7/12)]
print("K=",K,"N=",N); print("mesoscopic cells:",cells)
print("theta:",{c:round((n+c[0])*log(M)/((m+c[1])*log(A)),3) for c in cells})
P=sieve(max(N)); print("primes tested: all",len(P),"primes <=",max(N))
def vpf(X,p):
    t=0;q=p
    while q<=X: t+=X//q; q*=p
    return t
V=np.zeros((len(P),len(cells)),dtype=np.int64)
for ci,(i,j) in enumerate(cells):
    for pi,p in enumerate(P): V[pi,ci]=vpf(N[j],p)-vpf(N[j]-K[i],p)
Vu=np.unique(V,axis=0); print("distinct valuation vectors:",Vu.shape[0])
w=np.array([M**i*A**j for (i,j) in cells],dtype=np.int64); print("weights:",list(w))
ratios=[int(w[k+1])//int(w[k]) for k in range(len(w)-1)]
assert all(int(w[k])*ratios[k]==int(w[k+1]) for k in range(len(w)-1)),ratios
Bas=np.zeros((len(w)-1,len(w)),dtype=np.int64)
for k in range(len(w)-1): Bas[k,k]=-ratios[k]; Bas[k,k+1]=1
assert np.all(Bas@w==0)
def tails_ok(c):
    for j in sorted({j for (i,j) in cells}):
        idx=sorted([k for k,(i,jj) in enumerate(cells) if jj==j],key=lambda k:cells[k][0])
        s=0
        for k in reversed(idx):
            s+=c[k]
            if s<0: return False
    return True
for B in (3,4):
    coef=np.array(list(itertools.product(range(-B,B+1),repeat=Bas.shape[0])),dtype=np.int64)
    C=coef@Bas; C=C[np.any(C!=0,axis=1)]
    found=[];best=-10**9;bc=None
    CH=20000
    for s in range(0,C.shape[0],CH):
        blk=C[s:s+CH]; val=(blk@Vu.T).min(axis=1)
        for r in np.nonzero(val>=0)[0]: found.append(blk[r].copy())
        r=int(val.argmax())
        if val[r]>best: best=int(val[r]); bc=blk[r].copy()
    print(f"box {B}: nonzero balanced vectors {C.shape[0]}, max|c|={int(np.abs(C).max())},"
          f" INTEGRAL = {len(found)}, best min_p v_p = {best}")
    print("     best at",{cells[k]:int(bc[k]) for k in range(len(cells)) if bc[k]},
          " top-heavy:",tails_ok(bc))
