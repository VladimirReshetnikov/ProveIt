from sympy import sieve
M,A=5,11
Nj=A**7; Ks=[M**8,M**9]; Njm=A**6
lo,hi=Nj-Ks[1],Nj-Ks[0]
sieve.extend(hi+10)
ps=[p for p in sieve.primerange(lo+1,hi+1)]
def vp(N,K,p):
    v=0; q=p
    while q<=N:
        v += N//q - (N-K)//q
        if q> N//p: break
        q*=p
    return v
bad=0
for p in ps[:4000]:
    if vp(Nj,Ks[1],p)!=1: bad+=1
    if vp(Nj,Ks[0],p)!=0: bad+=1
    if vp(Njm,M**8,p)!=0: bad+=1   # lower slice must contribute 0
print("Step-1 exactness under H2 (K<=N/2): mismatches over",4000,"primes x3 tests =",bad)
