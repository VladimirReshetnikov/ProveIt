"""Exact verification of the two mechanism steps of the impossibility chain.

STEP 1 (annulus rigidity, already kernel-verified in TopSliceTailSum):
   for p in the annulus A_k = (N_j - K_{i_k}, N_j - K_{i_{k-1}}], the slice-j part of
   v_p(F) equals the tail sum T_k EXACTLY, and lower slices contribute 0.

STEP 2 (rescue capacity / divisor-counting bound):
   sum_{p in A_k} v_p(G_{i',j'})  <=  K_{i'} * (m+j')/(m+j)      for j' > j.
"""
import numpy as np
M,A,n,m = 5,11,3,3
K=[M**(n+i) for i in range(5)]; N=[A**(m+j) for j in range(3)]
def sieve(X):
    s=bytearray([1])*(X+1); s[0]=s[1]=0
    for i in range(2,int(X**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(X+1) if s[i]]
P=sieve(max(N))
def vpf(X,p):
    t=0;q=p
    while q<=X: t+=X//q; q*=p
    return t
def vd(Nn,Kk,p): return vpf(Nn,p)-vpf(Nn-Kk,p)

print("=== STEP 1: annulus valuation is exactly the tail sum ===")
bad=0; checks=0
import itertools, random
random.seed(7)
for j in range(3):
    lv=[i for i in range(5) if K[i]<=N[j]//2 and K[i]>=N[j]**(7/12)]
    if len(lv)<2: continue
    for _ in range(200):
        c={i:random.randint(-6,6) for i in lv}
        for k in range(len(lv)):
            lo = N[j]-K[lv[k]]; hi = N[j]-(K[lv[k-1]] if k>0 else 0)
            T=sum(c[i] for i in lv[k:])
            ps=[p for p in P if lo<p<=hi]
            for p in ps:
                v=sum(c[i]*vd(N[j],K[i],p) for i in lv)
                checks+=1
                if v!=T: bad+=1; print("  MISMATCH",j,k,p,v,T)
                # lower slices contribute nothing
                for j2 in range(j):
                    for i2 in range(5):
                        if K[i2]<=N[j2] and vd(N[j2],K[i2],p)!=0:
                            bad+=1; print("  LOWER SLICE CONTRIB",j2,i2,p)
print(f"  checked {checks} (slice,annulus,prime) instances; mismatches = {bad}")

print()
print("=== STEP 2: rescue capacity bound  sum_{p in annulus} v_p(G_{i'j'}) <= K_i' (m+j')/(m+j) ===")
worst=0
for j in range(2):
    lv=[i for i in range(5) if K[i]<=N[j]//2 and K[i]>=N[j]**(7/12)]
    for k in range(len(lv)):
        lo=N[j]-K[lv[k]]; hi=N[j]-(K[lv[k-1]] if k>0 else 0)
        ann=[p for p in P if lo<p<=hi]
        npr=len(ann)
        for j2 in range(j+1,3):
            for i2 in range(5):
                if K[i2]>N[j2]: continue
                tot=sum(vd(N[j2],K[i2],p) for p in ann)
                bound=K[i2]*(m+j2)/(m+j)
                r=tot/bound if bound else 0
                worst=max(worst,r)
                print(f"  slice j={j} ann k={k} (#primes {npr:5d}) vs level (i'={i2},j'={j2}):"
                      f" sum v_p = {tot:8d}  bound = {bound:12.1f}  ratio = {r:.4f}")
print("  worst ratio (must be <= 1):", round(worst,4))
