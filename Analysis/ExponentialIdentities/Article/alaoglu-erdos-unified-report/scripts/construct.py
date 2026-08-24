import math, time, sys, mpmath as mp
sys.set_int_max_str_digits(2000000)
def nd(x): return int(x.bit_length()*0.30103)+1
from sympy import primerange
mp.mp.dps=60
PR=[p for p in primerange(5,10**5)]
t0=time.time()
Q=1
for p in PR: Q*=p*p
print("Q = prod_{5<=p<1e5} p^2 : digits =", nd(Q), " log Q =", round(math.log2(Q)*math.log(2),1), f"({time.time()-t0:.1f}s)")

n=400000
x_desc="x = n + 1/2, n = 400000  (so 2^x = 2^n*sqrt2 is irrational; the pair is NOT a control)"
t0=time.time()
T2=math.isqrt(2**(2*n+1))        # floor(2^{n+1/2})
T3=math.isqrt(3**(2*n+1))        # floor(3^{n+1/2})
print("floor(2^x) digits =",nd(T2),"  floor(3^x) digits =",nd(T3), f"({time.time()-t0:.1f}s)")

def lift(target_res, base):
    """smallest integer >= base congruent to target_res mod Q"""
    d=(target_res-base)%Q
    return base+d

def qres(p,u):
    p2=p*p; return ((pow(u%p2,p-1,p2)-1)//p)%p
Q2={p:qres(p,2) for p in PR}; Q3={p:qres(p,3) for p in PR}
def dropset(M,A):
    out=[]
    for p in PR:
        if M%p==0 or A%p==0: out.append(('bad',p)); continue
        p2=p*p
        qM=((pow(M%p2,p-1,p2)-1)//p)%p; qA=((pow(A%p2,p-1,p2)-1)//p)%p
        if (qM*Q3[p]-qA*Q2[p])%p==0: out.append(p)
    return out

def report(name,M,A):
    t=time.time(); ds=dropset(M,A)
    lM=mp.log(mp.mpf(2))*n if False else None
    # exact-ish archimedean defect via high precision logs of the huge integers:
    mp.mp.dps=80
    # log M = log(T2) + log(M/T2) ; use log1p on the tiny relative shift
    dM=mp.mpf(M-T2)/mp.mpf(T2) if M>=T2 else -mp.mpf(T2-M)/mp.mpf(T2)
    dA=mp.mpf(A-T3)/mp.mpf(T3) if A>=T3 else -mp.mpf(T3-A)/mp.mpf(T3)
    # log T2 = (n+1/2) log 2 + O(2^-n) ; likewise T3
    lM=(mp.mpf(n)+mp.mpf(1)/2)*mp.log(2)+mp.log1p(dM)
    lA=(mp.mpf(n)+mp.mpf(1)/2)*mp.log(3)+mp.log1p(dA)
    D=mp.log(2)*lA-mp.log(3)*lM
    rel=abs(D)/(mp.log(2)*lA)
    print(f"\n--- {name} ---")
    print(f"  |M-2^x|/2^x = {mp.nstr(abs(dM),6)}   |A-3^x|/3^x = {mp.nstr(abs(dA),6)}")
    print(f"  archimedean wedge D_inf = {mp.nstr(D,6)}   relative = {mp.nstr(rel,6)}")
    print(f"  rank-drop primes below 1e5: {len([d for d in ds if not isinstance(d,tuple)])} of {len(PR)}   ({time.time()-t:.0f}s)")
    bad=[d[1] for d in ds if isinstance(d,tuple)]
    if bad: print("  primes dividing MA (wedge undefined):",bad[:10],"...",len(bad))
    pure=[d for d in ds if not isinstance(d,tuple)]
    if len(pure)<=20: print("  drop set =",pure)
    return pure

# (A) TOTAL rank collapse: M = 2 mod Q, A = 3 mod Q  -> Delta_p = q2*q3-q3*q2 = 0 for ALL p
MA=lift(2%Q,T2); AA=lift(3%Q,T3)
dA_=report("A: forced total rank collapse  (M=2 mod Q, A=3 mod Q)",MA,AA)

# (B) NEAR-ZERO rank collapse: M = 2^a mod Q, A = 2*3^a mod Q -> Delta_p = -q_p(2)^2
a=12345
MB=lift(pow(2,a,Q),T2); AB=lift(2*pow(3,a,Q)%Q,T3)
dB_=report("B: forced rank-drop set = Wieferich(2)  (M=2^a, A=2*3^a mod Q, a=12345)",MB,AB)

# (C) unforced control pair for comparison: M = T2 rounded, A = T3 rounded  (generic residues)
dC_=report("C: unforced (M=floor(2^x), A=floor(3^x))",T2,T3)
print("\n"+x_desc)
