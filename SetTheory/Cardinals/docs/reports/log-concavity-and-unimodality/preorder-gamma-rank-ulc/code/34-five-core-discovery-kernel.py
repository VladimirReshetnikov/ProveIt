from itertools import combinations, permutations
from math import prod, comb
import numpy as np
N=5
MASKS={k:[sum(1<<i for i in c)for c in combinations(range(N),k)]for k in range(N+1)}
IDX={m:tuple(i for i in range(N)if m>>i&1)for k in MASKS for m in MASKS[k]}
PAIRS=[(k,j,S,J)for k in range(1,6)for j in range(min(k,5-k)+1)for S in MASKS[k]for J in MASKS[j]if not S&J]
EXPS=np.array([[int(S>>i&1)for i in range(5)]+[int(J>>i&1)for i in range(5)]for k,j,S,J in PAIRS],dtype=float)
def feasible(rows,S,J):
 if not J:return True
 ns=[sum(1<<i for i in IDX[S]if rows[i]>>j&1)for j in IDX[J]]
 if len(ns)==1:return bool(ns[0])
 assert len(ns)==2
 return bool(ns[0]and ns[1]and (ns[0]|ns[1]).bit_count()>=2)
def features(rows):return np.array([feasible(rows,S,J)for k,j,S,J in PAIRS])
def kernels(rows):
 f=features(rows)
 return {(k,j):EXPS[[z for z,(kk,jj,_,__)in enumerate(PAIRS)if kk==k and jj==j and f[z]]]for k in range(1,6)for j in range(min(k,5-k)+1)}
def is_preorder(rows):
 R=[rows[i]|1<<i for i in range(5)]
 return all(not(R[i]>>j&1)or not(R[j]&~R[i])for i in range(5)for j in range(5))
def core_list():
 from pathlib import Path
 return [(int(a[0]),tuple(map(int,a[1:])))for a in [s.split()for s in (Path(__file__).parent/'cores.txt').read_text().splitlines()]]
def exact_coeffs(rows,u,v,w):
 E=[1]+[0]*5
 for a in w:
  for k in range(5,0,-1):E[k]+=a*E[k-1]
 out=[1]+[0]*5
 for k,j,S,J in PAIRS:
  if feasible(rows,S,J):out[k]+=prod(u[i]for i in IDX[S])*prod(v[jj]for jj in IDX[J])*E[k-j]
 return out
