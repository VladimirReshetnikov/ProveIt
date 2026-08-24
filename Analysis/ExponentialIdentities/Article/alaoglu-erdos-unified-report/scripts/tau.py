import mpmath as mp, random, math
from collections import Counter
from sympy import primerange
mp.mp.dps=300; random.seed(99)
PRIMES=[p for p in primerange(5,10**5)]
THETA=mp.log(3)/mp.log(2)

K=6   # work mod p^K
def ell(p,u):
    """ log_p(u^(p-1))/(p-1) mod p^K ; equals -p*q_p(u) mod p^2 """
    pK=p**K
    z=(pow(u%pK,p-1,pK)-1)%pK          # = p*t, v_p(z)>=1
    s=0
    for i in range(1,K+2):
        e=0; j=i
        while j%p==0: j//=p; e+=1
        if i-e>=K: continue
        num=pow(z,i)//(p**e)          # exact: v_p(z^i)>=i>=p^e>=e+1
        term=(num % pK)*pow(j,-1,pK)%pK
        s=(s+term) if i%2==1 else (s-term)
    s%=pK
    return s*pow(p-1,-1,pK)%pK

def vp(x,p,cap):
    if x%p**cap==0: return cap
    v=0
    while x%p==0: x//=p; v+=1
    return v

def tau(p,M,A):
    pK=p**K
    d=(ell(p,2)*ell(p,A)-ell(p,3)*ell(p,M))%pK
    return vp(d,p,K)-2     # each ell has v_p>=1, so v_p(det)>=2; tau = v_p(det B_p)

def qres(p,u):
    p2=p*p; return ((pow(u%p2,p-1,p2)-1)//p)%p
Q2={p:qres(p,2) for p in PRIMES}; Q3={p:qres(p,3) for p in PRIMES}
def drops(M,A):
    out=[]
    for p in PRIMES:
        if M%p==0 or A%p==0: continue
        p2=p*p
        if ((((pow(M%p2,p-1,p2)-1)//p)%p)*Q3[p]-((((pow(A%p2,p-1,p2)-1)//p)%p))*Q2[p])%p==0: out.append(p)
    return out

print("=== tau_p at the rank-drop primes of 200 candidate-shaped pairs (M~2^100) ===")
tc=Counter(); allE=0.0; nd=0; ndrop=0
for i in range(200):
    M=random.randrange(2**100,2**101); A=int(mp.nint(mp.power(mp.mpf(M),THETA)))
    for p in drops(M,A):
        t=tau(p,M,A); tc[t]+=1; ndrop+=1; allE+=t*math.log(p)
print("tau distribution over all drop primes:", dict(sorted(tc.items())))
print("total drop primes:",ndrop,"  mean log E per pair = sum tau*log p /200 =", round(allE/200,4))
print("(compare log G = theta(1e5) - log6 = 99683.60  ->  kappa = 2 - logE/logG)")
print("mean kappa = 2 -", round(allE/200/99683.60,8), "=", round(2-allE/200/99683.60,8))

print()
print("=== monoid bilinearity check: Delta_p(2^r M^s, 3^r A^s) = s*Delta_p(M,A) ===")
M=random.randrange(2**40,2**41); A=int(mp.nint(mp.power(mp.mpf(M),THETA)))
ok=True
for p in [5,7,11,13,101,1009,10007,99991]:
    for (r,s) in [(0,1),(1,1),(3,2),(7,5),(11,13)]:
        MM=2**r*M**s; AA=3**r*A**s
        lhs=(qres(p,MM)*Q3[p]-qres(p,AA)*Q2[p])%p
        rhs=(s*((qres(p,M)*Q3[p]-qres(p,A)*Q2[p])))%p
        if lhs!=rhs: ok=False; print("FAIL",p,r,s,lhs,rhs)
print("bilinearity holds on all tested (p,r,s):", ok)
