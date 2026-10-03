from collections import Counter
from fractions import Fraction
from functools import lru_cache
from math import factorial, comb, prod
import sympy as S

@lru_cache(None)
def word_hist(counts, last=-1):
    if not any(counts): return ((0,1),)
    out=Counter()
    for i,c in enumerate(counts):
        if c:
            rest=list(counts);rest[i]-=1
            for x,a in word_hist(tuple(rest),i):out[x+(i==last)]+=a
    return tuple(sorted(out.items()))

def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out

for k in range(2,6):
 for n in range(1,6):
    hist=dict(word_hist((k,)*n));total=sum(hist.values());N=k*n;d=(k-1)*n
    R=[comb(k-1,m)*factorial(k)//factorial(k-m) for m in range(k)]
    rn=[1]
    for _ in range(n):rn=mul(rn,R)
    for M in range(d+3):
        exact=sum(Fraction(a*comb(x,M),total) for x,a in hist.items() if x>=M)
        formula=Fraction(rn[M],prod(range(N-M+1,N+1))) if M<=d else Fraction(0)
        assert exact==formula,(k,n,M,exact,formula)
        assert 0<=exact<=Fraction((k-1)**M,factorial(M))
    print(f'Exact enumeration agrees, k={k}, n={n}, N={N}, words={total}')

for M in range(15):
    H=[1]+[0]*12
    for j in range(M):
        for r in range(1,len(H)):H[r]+=j*H[r-1]
    for a in range(7):
      for b in range(7):assert H[a+b]<=H[a]*H[b]
    for N in range(max(M+1,1),max(M+1,1)+10):
        x=Fraction(1,N);Q=prod(Fraction(N,N-j) for j in range(M))
        for L in range(8):
            err=Q-sum(H[r]*x**r for r in range(L+1))
            assert 0<=err<=x**(L+1)*H[L+1]*Q,(M,N,L)
print('Exact rational h-submultiplicativity and Q remainder checks passed')

k,v,w,z,m=S.symbols('k v w z m')
R=sum(S.ff(k-1,j)*S.ff(k,j)*z**j/S.factorial(j) for j in range(5))
b=[None]+[S.factor(S.expand(S.series(S.log(R),z,0,5).removeO()).coeff(z,j)) for j in range(1,5)]
exponent=sum(b[j+1]/k*v**(j+1)*w**j for j in range(1,4))
fexpr=S.series(S.exp(exponent),w,0,4).removeO().expand()
f=[S.factor(fexpr.coeff(w,j)) for j in range(4)]
p1=m*(m-1)/2;p2=m*(m-1)*(2*m-1)/6;p3=p1**2
H=[S.Integer(1),p1,(p1**2+p2)/2,(p1**3+3*p1*p2+2*p3)/6]

def conjugate_D(poly):return S.expand(v*S.diff(poly,v)+(k-1)*v*poly)
def applyH(r,poly):
    coeffs=S.Poly(S.expand(H[r]),m)
    result=0;current=poly
    for j in range(2*r+1):
        result+=coeffs.nth(j)*current
        current=conjugate_D(current)
    return S.expand(result)
P=[S.factor(sum(applyH(r,f[s-r]) for r in range(s+1))) for s in range(4)]
C=[None,P[1],S.factor(P[2]-P[1]**2/2),S.factor(P[3]-P[1]*P[2]+P[1]**3/3)]
print('\nSymbolic coefficients in N^-s:')
for i in range(1,4):
 print(f'b{i+1} = {b[i+1]}')
 print(f'f{i} = {f[i]}')
 print(f'P{i} = {P[i]}')
 print(f'log C{i} = {C[i]}')
 print(f'log coefficient after N=kn, n^-{i}: {S.factor(C[i]/k**i)}')
print('P_s(0)=0:',[S.simplify(P[i].subs(v,0)) for i in range(1,4)])
for i in range(1,4):assert S.simplify(P[i].subs(v,0))==0
lam=k-1
claimed_log=[None,-lam**2*v**2/2,lam**2*v**2*(2*(k-2)*v-3)/6,-lam**2*v**2*((k*k-6*k+7)*v*v-4*(k-2)*v+2)/4]
claimed_p=[1,-lam**2/2,lam**2*(3*k*k-14*k+7)/24,-lam**4*(k*k-10*k+17)/48]
for s in range(1,4):
    assert S.expand(C[s]-claimed_log[s])==0
    assert S.expand(P[s].subs(v,-1)-claimed_p[s])==0
print('All displayed third-order log-PGF and probability coefficients match exactly')
x=S.symbols('x')
logp=sum(C[s].subs(v,-1)/k**s*x**s for s in range(1,4))
ratio=S.series(S.exp(logp.subs(x,x/(1+x))-logp),x,0,4).removeO()
assert S.simplify(ratio-1-lam**2/(2*k)*x**2-lam**2*(k-2)/(6*k*k)*x**3)==0
print('Successive-term probability ratio matches exactly through n^-3')
for kval in range(2,6):
    print('Specialized p coefficients, k=',kval,[S.factor((P[s].subs(v,-1)/k**s).subs(k,kval)) for s in range(1,4)])
for j in range(12):
    # Divide coefficient of e^(lambda(u-1))*(-lambda^2/2)*(u-1)^2 by its Poisson coefficient.
    got=-lam**2/S.Integer(2)*(1-2*j/lam+j*(j-1)/lam**2)
    assert S.simplify(got+((lam-j)**2-j)/2)==0
print('First fixed-local correction verified for j=0,...,11 (same algebra holds for arbitrary j)')
