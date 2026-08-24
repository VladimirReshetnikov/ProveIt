import math
from sympy import sieve
M,A=5,11
Nj  = A**7            # slice j top
Kkm1= M**8; Kk = M**9 # annulus between these two windows
Njp = A**8            # slice j' = j+1
Kip = M**10
for (K,N,lab) in [(Kkm1,Nj,'K_{i_{k-1}}'),(Kk,Nj,'K_{i_k}'),(Kip,Njp,"K_{i'}")]:
    th=math.log(K)/math.log(N)
    print(f"{lab}: K={K} N={N} theta={th:.4f} 7/12<th<1:{7/12<th<1} K<=N/2:{K<=N//2}")
lo,hi = Nj-Kk, Nj-Kkm1
print("annulus =",(lo,hi)," length =",hi-lo," = M^n*Delta_k =",Kk-Kkm1)
sieve.extend(hi+10)
ps=[p for p in sieve.primerange(lo+1,hi+1)]
print("primes in annulus:",len(ps))
print("H3 lower bound  length/(2 ln N_j) =", (hi-lo)/(2*math.log(Nj)), " -> H3 holds:", len(ps)>= (hi-lo)/(2*math.log(Nj)))
# exact capacity of level (i',j')
cap=0
Wlo=Njp-Kip
for p in ps:
    cnt = Njp//p - Wlo//p
    if cnt: cap+=cnt          # p^2 > N_{j'} so v_p = #multiples
print("EXACT  sum_{p in annulus} v_p(G_{i'j'}) =",cap)
b1 = Kip*math.log(Njp)/math.log(Nj/2)
b2 = 2*Kip*8/7
print("claimed bound K' lnN'/ln(N_j/2) =",b1," ratio actual/bound =",cap/b1)
print("claimed bound 2K'(m+j')/(m+j)   =",b2," ratio =",cap/b2)
print("report's multiplicity-one bound  K' =",Kip," ratio =",cap/Kip)
print("sharp (Brun-Titchmarsh-type) truth: capacity/#annulus-primes =",cap/len(ps))
