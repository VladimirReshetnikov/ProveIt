"""EXACT toy laboratory for the 2-parameter factorial cocycle.

G_{i,j} = (N_j)_{K_i}  with K_i = M^{n+i}, N_j = A^{m+j}.
Scale chosen so that N_max is small enough to test EVERY prime p <= N_max exactly.
"""
import sys, numpy as np
from itertools import product

M, A, n, m = 5, 11, 3, 3
Imax, Jmax = 5, 3

def sieve(N):
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**0.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]

def vp_fact(N,p):
    t=0;q=p
    while q<=N: t+=N//q; q*=p
    return t
def vp_desc(N,K,p): return vp_fact(N,p)-vp_fact(N-K,p)

K = [M**(n+i) for i in range(Imax)]
N = [A**(m+j) for j in range(Jmax)]
cells=[]
for j in range(Jmax):
    for i in range(Imax):
        if K[i] <= N[j]//2 and K[i] >= N[j]**(7/12):
            cells.append((i,j))
print("M,A,n,m =",M,A,n,m)
print("K =",K)
print("N =",N)
print("admissible (mesoscopic) cells (i,j) with N^{7/12} <= K <= N/2:", cells)
theta = {(i,j): ( (n+i)*np.log(M) )/( (m+j)*np.log(A) ) for (i,j) in cells}
print("theta values:", {k:round(v,4) for k,v in theta.items()})

Nmax = max(N)
P = sieve(Nmax)
print("primes tested: all", len(P), "primes <= ", Nmax)

# valuation matrix V[p_index][cell]
V = np.zeros((len(P), len(cells)), dtype=np.int64)
for ci,(i,j) in enumerate(cells):
    kk, nn = K[i], N[j]
    for pi,p in enumerate(P):
        V[pi,ci] = vp_desc(nn,kk,p)
# distinct rows only
Vu = np.unique(V, axis=0)
print("distinct valuation vectors:", Vu.shape[0])

w = np.array([M**i * A**j for (i,j) in cells], dtype=object)
print("balance weights M^i A^j:", list(w))
np.save("V.npy", Vu)
import json
json.dump({"cells":cells,"w":[int(x) for x in w]}, open("lab.json","w"))
