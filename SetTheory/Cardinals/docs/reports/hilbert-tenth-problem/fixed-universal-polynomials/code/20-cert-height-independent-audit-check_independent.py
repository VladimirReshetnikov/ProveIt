#!/usr/bin/env python3
"""Independent bounded evidence for the quantitative square/product82 audit.
No upstream code imports, no saved-schedule execution, no genuine full tuple.
All checks remain active under python -O. All Pell operands are capped.
"""
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

ROOT = Path('/workspace/shared/square-product82-report45-release-20261004')
BASE = ROOT/'packets/square-product82-counterfamily-recovered-20261004'
HERE = Path(__file__).resolve().parent
CAP = 450_000
COUNTS = {}
MAX_BITS = 0

def need(ok, label):
    if not ok:
        raise RuntimeError(label)
    COUNTS[label] = COUNTS.get(label, 0) + 1

def bounded(z):
    global MAX_BITS
    bits = abs(z).bit_length()
    need(bits <= CAP, 'operand bit cap')
    MAX_BITS = max(MAX_BITS, bits)
    return z

def pell(a, n):
    """Direct two-coordinate recurrence, independently implemented."""
    x0,x1,y0,y1 = 1,a,0,1
    if n == 0:
        return x0,y0
    for _ in range(1,n):
        x0,x1 = x1,bounded(2*a*x1-x0)
        y0,y1 = y1,bounded(2*a*y1-y0)
    return x1,y1

def ceil_log2(z):
    return (z-1).bit_length()

# Source files are read and hashed as inert data only.
pins = {
    'COUNTERFAMILY.md':'690c5a1dc237bd53a9582bfbe01fcd8a176174e6b116089a1842532f83c1770b',
    'source/complete82_auxiliary_square_product_chart.py':'5ff4a91d10551eafedd1d44673f64f10aa2ed283ab071d2c969d38410999f6dc',
    'source/complete82_auxiliary_square_product_chart.json':'7c029ad047c9db4652621334cb4c57d1781b5833dfac19de734ef0cb4c05fc7a',
    'source/complete82_auxiliary_square_product_chart.md':'10b83a1800550674298c797e97f4e3ccadb45e7f4c532045e869e03b55caf1c9',
}
for name,pin in pins.items():
    need(hashlib.sha256((BASE/name).read_bytes()).hexdigest() == pin, 'source pin')

# Nine synthetic inner fixtures; no packing compiler or full tuple is claimed.
fixtures = [('A',u) for u in range(4,12)] + [('B',2)]
inner = []
for branch,z in fixtures:
    if branch == 'A':
        eps = 1 if z%2 == 0 else -1
        p,n,y,R = 4*z,3*z,2*z-1,6*z-eps
    else:
        eps = 1
        p,n,y,R = 20*z,14*z,15*z-1,28*z-1
    L = p+y+1
    C = (p-1)*L
    T = 2*p*L-1
    N = (R-1)*T
    F0 = 4*C+2*L-2
    need(N+2 <= CAP, 'preflight inner bit cap')
    X,Y = 1<<p,1<<y
    a0 = Y*(X+1)
    A = a0+2
    D,c = pell(A,p)
    Delta = A*A-1
    P = 2*X*Y*Y+1
    tau,kn = pell(P,n)
    k = 2*kn
    need((n-1)*(p+2*y+2) == C-y-1 and n*(p+2*y+2) == p*L, 'exact resonance')
    need(D*D-Delta*c*c == 1, 'main norm')
    need(c%8 == 0 and c>2*R and R%4 == 3, 'actual inner residue sector')
    need(c.bit_length() == C+1, 'c exact length')
    need(k.bit_length() == C-y+1, 'k exact length')
    need((k-2*n)%(X*Y)==0, 'h divisibility')
    h = (k-2*n)//(X*Y)
    need(h.bit_length() == C-p-2*y+1, 'h exact length')
    need(tau.bit_length() == p*L, 'tau exact length')
    eta,zeta = c-k*Y,k-(c-k*Y)
    need(eta>0 and zeta>0, 'ratio positivity')
    need(eta.bit_length() <= C-p+ceil_log2(p)+3, 'eta upper length')
    need(zeta.bit_length() <= C-y+1, 'zeta upper length')
    Hmain = 4*A-5
    gp = (D-a0*c-(1<<p))//Hmain
    need((D-a0*c-(1<<p))%Hmain == 0, 'main projection integrality')
    for I in [3,5,7,p-3,p-1]:
        chiI,psiI = pell(A,I)
        need((psiI-I)%Delta == 0, 'delta divisibility')
        delta = (psiI-I)//Delta
        need(delta.bit_length() == (I-3)*L+3, 'delta exact length')
        numerator = chiI-a0*psiI-(1<<I)
        need(numerator%Hmain == 0, 'input projection integrality')
        rho = numerator//Hmain
        sigma = gp-rho
        need(rho.bit_length() == (I-2)*L+1, 'rho exact length')
        need(sigma.bit_length() == (p-2)*L+1, 'sigma exact length')
        need(max(h,tau,eta,zeta,delta,rho,sigma).bit_length() <= F0+1, 'nonauxiliary inner dominance')
    F = Delta*c**4+1
    S = Delta*c*c
    chiR,yaux = pell(S,R)
    need(chiR%S == 0, 'V divisibility')
    V = chiR//S
    need((V+R*F)%c == 0, 'U divisibility')
    U = (V+R*F)//c+1
    need(F.bit_length() == F0+1, 'Faux exact length')
    need(yaux.bit_length() == N+1, 'yaux exact length')
    need(V.bit_length() == N+1 and V<yaux, 'V exact length and comparison')
    need(U.bit_length() == N-C+1, 'Uaux exact length')
    need(max(F,U) < yaux, 'auxiliary dominance')
    need(N-F0 == (2*R-6)*C+(2*R-4)*L-R+3 and N-F0>=R, 'gap identity')
    if branch == 'A':
        cubic = Fraction(4*R**3+(8*eps-4)*R**2+(1-8*eps)*R+2,3)
    else:
        cubic = Fraction(25*R**3+25*R**2-39*R+3,14)
    need(cubic.denominator==1 and cubic==N+1, 'cubic exact identity')
    # Transport and pure powers tested separately, as component values only.
    for t in range(1,min(y//3,5)+1):
        q = 1<<t
        e = p%t or t
        w,s = 1<<(p-t),1<<(y-3*t)
        W,Z = 1<<3,1
        lc = ceil_log2(W+Z)
        need((w-(1<<e))%(q-1)==0, 'transport divisibility')
        tr = 1+(W+Z)*(w-(1<<e))//(q-1)
        need(tr>0 and tr.bit_length()<=p-2*t+lc+2, 'transport upper length')
        need(w.bit_length()==p-t+1 and s.bit_length()==y-3*t+1, 'w and s exact length')
    inner.append({'branch':branch,'scale':z,'p':p,'n':n,'yexp':y,'R':R,'yaux_bits':N+1})

# All integral R in a broad small range, independent of branch admissibility.
for R in range(100,2001):
    for eps in [-1,1]:
        f = Fraction(4*R**3+(8*eps-4)*R**2+(1-8*eps)*R+2,3)
        need(Fraction(5,4)*R**3 < f < 2*R**3, 'cubic coarse envelope A')
    f = Fraction(25*R**3+25*R**2-39*R+3,14)
    need(Fraction(5,4)*R**3 < f < 2*R**3, 'cubic coarse envelope B')
need(Fraction(5,4)*Fraction(99,100)**3>1, 'height envelope multiplier')
for p in range(16,1001):
    need(Fraction(8*p*p,1<<p)<=Fraction(1,32), 'uniform error budget')

# Minimal radix computed solely by integer multiplication; exact jumps retained.
def radix(a,M):
    r,t = a,5**a
    while t<4*M:
        r,t = r+1,5*t
    return r,t
radix_samples = 0
for a in range(1,7):
    for M in range(61,2001):
        r,t = radix(a,M)
        need(t>=max(5**a,4*M) and (r==a or t//5<4*M), 'minimal radix')
        need(t<=max(5**a,20*M) and (t==5**a or t<20*M), 'radix envelope')
        radix_samples += 1
need(radix(1,155)[1]==625 and radix(1,156)[1]==625 and radix(1,157)[1]==3125, 'radix jump 156 to 157')

# Synthetic frozen-port outer construction, stopping at ordinary-size exponent data.
def crt(pairs):
    z,m = 0,1
    for residue,mod in pairs:
        z += m*((residue-z)*pow(m,-1,mod)%mod)
        m *= mod
        z %= m
    return z or m
outer = []
for a,x,K,MC,MF0 in [(1,x,K,2,mf) for x in [1,15,16] for K in [1,2,17] for mf in [1,2,3]] + [(2,1,1,2,1),(3,1,1,2,2)]:
    d=5**a
    B=1<<d
    ell,b=2*d,5
    I=ell*x+b
    Mbound=max(I,K.bit_length(),61)
    r,t=radix(a,Mbound)
    q=1<<t
    J=(q-1)//(B-1)
    MF=MF0+B-1
    mask=(MC+q*MF)*J
    Q=q*q-1
    m3=(MC+2*MF)%3
    W=1<<I
    if m3:
        eps=1 if m3==2 else -1
        e=8 if K%5!=1 else 9
        Kplus=K+(1<<e)
        beta=Q*(1+q*Kplus)
        star=Q*(q*q-q*(Kplus*W+1-eps))+mask
        target=(3*e*pow(2,-1,t)-eps)%t
        zres=(star-target)*pow(beta,-1,t)%t
        Z=crt([(1,4),(zres,t)])
        branch='A'
    else:
        eps=1
        h0=next(h for h in range(1,13) if (1+q*(K+(1<<(5*h))))%5 and (1+q*(K+(1<<(5*h))))%7)
        e=5*h0
        Kplus=K+(1<<e)
        beta=Q*(1+q*Kplus)
        star=Q*(q*q-q*Kplus*W)+mask
        Tsmall=t//5
        Z=crt([(1,4),((star+1)*pow(beta,-1,7)%7,7),((star-(7*h0-1))*pow(beta,-1,Tsmall)%Tsmall,Tsmall)])
        branch='B'
    F=Kplus*(W+Z)+1-eps
    alpha=q-F-2*Z-W-ell*x
    R=(q*q-Z-q*F)*Q+mask
    need(R==q**4-q**3*F-q*q*(Z+1)+q*F+Z+mask, 'packed R expansion')
    need(0<J<q and 0<alpha<q and 0<F and 0<Z<=6*t, 'outer positivity')
    need(J.bit_length()<=t and alpha.bit_length()<=t, 'J alpha upper lengths')
    need(F.bit_length()<=(t+1)//2+3, 'packing F upper length')
    need(Z.bit_length()<=(6*t).bit_length(), 'Z upper length')
    need(ceil_log2(W+Z)<=(t+3)//4+1, 'lc upper length')
    need((1<<(3*t))<R<q**4-q**3, 'outer R range')
    # Rational upper bound uses 2^(-t/2)<2^(-(t-1)/2), avoiding floating point.
    theta=Fraction(q**4-R,q**4)
    rational_error=Fraction(4,1<<((t-1)//2))+Fraction(2,1<<t)+Fraction(6*t+1,1<<(2*t))
    need(0<theta<rational_error<Fraction(1,100), 'packing error rational upper')
    if branch=='A':
        scale=(R+eps)//6
        p,n,y=4*scale,3*scale,2*scale-1
    else:
        scale=(R+1)//28
        p,n,y=20*scale,14*scale,15*scale-1
    need(p%t==e and p>56*t and y>=3*t and R<2*p, 'outer exponent conditions')
    need(p%4==0 and R%4==3 and p>I, 'outer residue conditions')
    L=p+y+1
    N=(R-1)*(2*p*L-1)
    bits=N+1
    need((1<<(12*t))<bits<(1<<(12*t+1)), 'full height bound without giant witness')
    # Every row can be compared symbolically to F0+1 with no Pell construction.
    C=(p-1)*L
    F0=4*C+2*L-2
    lc=ceil_log2(W+Z)
    row_bounds=[t,(t+1)//2+3,t,p-2*t+lc+2,F0+1,C-p-2*y+1,1,y-3*t+1,p-t+1,p*L,C-p+ceil_log2(p)+3,C-y+1,(6*t).bit_length(),(I-3)*L+3,(I-2)*L+1,(p-2)*L+1]
    need(all(v<=F0+1 for v in row_bounds) and N-F0>=R, 'all nondominant row bounds')
    need(N-C+1<N+1, 'U symbolic dominance')
    outer.append({'a':a,'x':x,'K':K,'MF0':MF0,'branch':branch,'r':r,'t':t,'R_bits':R.bit_length()})

# Standalone Pell classification by exhaustive square test and descent.
classified=0
for S in range(2,21):
    d=S*S-1
    for y in range(1,5001):
        x=math.isqrt(d*y*y+1)
        if x*x-d*y*y != 1:
            continue
        original=(x,y)
        steps=0
        while y:
            xp,yp=S*x-d*y,S*y-x
            need(xp>0 and 0<=yp<y and xp*xp-d*yp*yp==1, 'Pell descent')
            x,y=xp,yp
            steps+=1
        need((x,y)==(1,0) and pell(S,steps)==original, 'complete bounded classification')
        classified+=1

# Explicit admissible-sign and index tests, extending well past the first two indices.
classes=0
for c in [8,16,24,32,40]:
    for R in range(3,c//2,4):
        for i in [1,2,3]:
            Delta=3
            S=i*Delta*c*c
            F=Delta*i*i*c**4+1
            candidates=[]
            for m in range(1,2*c+R+1):
                x,y=pell(S,m)
                need((x%S==0)==(m%2==1), 'even Pell index exclusion')
                if m%2==0:
                    continue
                V=x//S
                need(V%c==((-1)**((m-1)//2)*m)%c, 'odd polynomial residue')
                need(V%4==1 and (-V+R*F)%c!=0, 'negative V exclusion')
                valid=(V+R*F)%c==0
                need(valid==(m%c in [R,(-R)%c]), 'complete positive index classes')
                if valid:
                    U=(V+R*F)//c+1
                    candidates.append((m,y,U))
            need([v[0] for v in candidates[:2]]==[R,c-R], 'first and next auxiliary indices')
            need(all(y>=candidates[0][1] and U>=candidates[0][2] for _,y,U in candidates), 'fixed i coordinate minimum')
            if i==1:
                base=candidates[0]
            else:
                need(candidates[0][1]>base[1] and candidates[0][2]>base[2], 'positive i strict coordinate minimum')
            classes+=1
for S in range(4,101,4):
    for V in range(-10,11):
        for y in range(1,11):
            need((S*S*V*V-(S*S-1)*y*y)%4 in [0,1], 'norm minus one exclusion')
for m in range(3,22,2):
    last=None
    for S in range(2,31):
        x,y=pell(S,m)
        if last:
            need(y>last[1] and x//S>last[0], 'monotonicity in S')
        last=(x//S,y)

result={
 'status':'PASS',
 'scope':'Independent corroborative bounded checks; proof, not finite evidence, establishes unbounded claims.',
 'no_upstream_code_or_saved_schedule_executed':True,
 'no_genuine_full_tuple_materialized':True,
 'operand_bit_cap':CAP,'maximum_checked_pell_operand_bits':MAX_BITS,
 'source_sha256':pins,
 'inner_fixtures':inner,
 'outer_fixtures':outer,
 'radix_samples':radix_samples,
 'bounded_Pell_solutions_classified':classified,
 'auxiliary_sector_cases':classes,
 'counts':dict(sorted(COUNTS.items())),
}
print(json.dumps(result,indent=2,sort_keys=True))
