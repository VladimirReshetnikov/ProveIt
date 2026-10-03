"""Independent diagnostics for the six A202061 proof notes.

No imports from the author's research directory. Exact identities and finite
counts supplement, rather than replace, the mathematical audit.
"""
from collections import defaultdict
from functools import lru_cache
from fractions import Fraction as F
from math import comb, log, floor
import sympy as s
import mpmath as mp

u,x,z,t,v=s.symbols('u x z t v')
f=7*u**3+14*u**2-7*u-1
k=(-21*u**2+17*u+5)/29
mu=(1+u)/(1-u-k); rho=1/mu
zs=k*(1-u-k)/((u-k)*(2*u+k)); ts=1/zs; b=1-rho
beta=rho*ts/b; eta=rho**2*ts/b**2
Qs=b*zs/(b*zs+rho); Ws=((1-zs)*Qs-zs)/rho
ss=b*b-rho*rho*ts
z2=ss**2/((b+rho*ts)**2*zs)

def zero(expr):
    return s.rem(s.cancel(expr).as_numer_denom()[0],f,u)==0

identities={
    'critical growth cubic':mu**3-8*mu**2+5*mu+1,
    'critical tilt cubic':zs**3-5*zs**2+6*zs-1,
    'fixed point':Ws*b*(1-eta*(1+Ws))-zs*(1+beta)*(1+Ws),
    'tilt identity W=1+beta':Ws-1-beta,
    'tilt identity eta(2+beta)^2=1':eta*(2+beta)**2-1,
    'sqrt branch value at critical point':
       2*rho*ts*(1-zs)*Qs-(ss-(b-rho*ts)*zs),
    'discriminant vanishes at zstar':
       (b*(zs-b)+rho*ts*(rho-zs))**2-4*rho*ts*(1-zs)*b*zs,
}
for label,expr in identities.items():
    assert zero(expr),label
    print('PASS exact field:',label)
disc=(b*(z-b)+rho*ts*(rho-z))**2-4*rho*ts*(1-z)*b*z
factorization=disc-ss**2*(1-z/zs)*(1-z/z2)
for coeff in s.Poly(s.together(factorization).as_numer_denom()[0],z).all_coeffs():
    assert zero(coeff)
print('PASS exact field: complete fixed-tilt discriminant factorization')

# Rational interval arithmetic, independently implemented with operators.
class Box:
    def __init__(self,lo,hi=None):self.lo=F(lo);self.hi=F(lo if hi is None else hi)
    def __add__(self,other):
        other=other if isinstance(other,Box) else Box(other)
        return Box(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self):return Box(-self.hi,-self.lo)
    def __sub__(self,o):return self+-o if isinstance(o,Box) else self+(-o)
    def __rsub__(self,o):return -self+o
    def __mul__(self,other):
        other=other if isinstance(other,Box) else Box(other)
        vals=[a*b for a in [self.lo,self.hi] for b in [other.lo,other.hi]]
        return Box(min(vals),max(vals))
    __rmul__=__mul__
    def __pow__(self,n):
        if n<0:
            assert self.lo*self.hi>0
            return Box(1/self.hi,1/self.lo)**(-n)
        out=Box(1)
        for _ in range(n):out=out*self
        return out
    def __truediv__(self,o):return self*(o**-1 if isinstance(o,Box) else Box(o)**-1)
    def __rtruediv__(self,o):return Box(o)*(self**-1)
    def __repr__(self):return '[%.16g, %.16g]'%(float(self.lo),float(self.hi))

lo=s.Rational(5100033746178887,10**16)
hi=s.Rational(5100033746178889,10**16)
assert f.subs(u,lo)<0<f.subs(u,hi)
assert s.Poly(f,u).count_roots(0,s.oo)==1
def interval(expr):
    if expr==u:return Box(lo,hi)
    if expr.is_Rational:return Box(expr)
    if expr.is_Add:return sum((interval(a) for a in expr.args),Box(0))
    if expr.is_Mul:
        ans=Box(1)
        for a in expr.args:ans=ans*interval(a)
        return ans
    if expr.is_Pow and expr.exp.is_Integer:return interval(expr.base)**int(expr.exp)
    raise ValueError(expr)
for label,expr,a,bb in [
    ('positive alpha',u,F(1,2),F(3,5)),
    ('interior alpha-kappa',u-k,F(1,5),F(1,4)),
    ('interior remaining length',1-u-k,F(1,5),F(1,4)),
    ('growth root',mu,F(729,100),F(73,10)),
    ('zstar',zs,F(19,100),F(1,5)),
    ('second z root',z2,F(88,100),F(89,100)),
    ('positive discriminant constant',ss,F(6,10),F(7,10)),
    ('fixed-point denominator',1-eta*(1+Ws),F(6,10),F(7,10)),
    ('row mass',rho*ts*Qs/b,F(4,10),F(5,10))]:
    val=interval(expr)
    assert a<val.lo<=val.hi<bb,(label,val)
    print('PASS rational box:',label,val)

# A concrete quadratic perturbation D=1 works locally; the proof needs only
# existence of sufficiently large D, but this checks the sign independently.
uu=eta*(1+Ws)
Lxx=1/b+ts/(b*b*(1+beta))+2*uu/(rho*b*(1-uu))
Ltt=beta/(1+beta)**2+uu/(1-uu)**2
assert zero(-1/(1+beta)+uu/(1-uu))
curvature=interval(Ltt/2-rho*Lxx)
assert curvature.hi<0
print('PASS rational box: normalized quadratic coefficient with D=1',curvature)

# Recover Q directly from its quadratic, using signed polynomial arithmetic,
# rather than the author's positive gap-operator recurrence.
N=12
def add(*polys):
    ans=defaultdict(int)
    for poly in polys:
        for key,val in poly.items():ans[key]+=val
    return {key:val for key,val in ans.items() if val}
def scale(poly,c):return {key:c*val for key,val in poly.items()}
def times(p,q):
    ans=defaultdict(int)
    for (n,r),a in p.items():
        for (m,j),bb in q.items():
            if n+m<=N:ans[n+m,r+j]+=a*bb
    return {key:val for key,val in ans.items() if val}
one={(0,0):1}; bp={(0,0):1,(1,0):-1}
bmxt=add(bp,{(1,1):-1}); xt={(1,1):1}
small={(1,0):2,(2,0):-1,(2,1):1}
inv=dict(one); power=dict(one)
for _ in range(N):power=times(power,small);inv=add(inv,power)
Q={0:{}}
for q in range(1,11):
    convolution=add(*(times(Q[j],Q[q-j]) for j in range(1,q)))
    previous=add(*(times(Q[j],Q[q-1-j]) for j in range(1,q-1)))
    rhs=add(bp if q==1 else {},times(bmxt,Q[q-1]),times(xt,add(convolution,scale(previous,-1))))
    Q[q]=times(inv,rhs)

def catalan_binomial(j,kk):
    numerator=comb(j+kk-1,kk)*comb(j+kk,kk+1)
    assert numerator%j==0
    return numerator//j
@lru_cache(None)
def B(ell,q,r):
    ans=int(ell==0 and r==0)
    for j in range(1,q+1):
        for kk in range(r+1):
            if 0<=r-kk<=j and ell>=r+kk+1:
                ans+=catalan_binomial(j,kk)*comb(j,r-kk)*comb(j+ell-2,ell-r-kk-1)
    return ans
checks=0
for q in range(1,11):
    for ell in range(N+1):
        for r in range(N+1):
            assert B(ell,q,r)==Q[q].get((ell,r),0),(ell,q,r)
            checks+=1
print('PASS independent quadratic vs positive jump formula:',checks,'coefficients')

# The finite Narayana rational identity, by direct exact coefficient extraction.
for j in range(1,36):
    for kk in range(51):
        if j==1:coef=1
        else:
            coef=sum(F(comb(j-1,ll)*comb(j-1,ll+1),j-1)*comb(2*j+kk-ll-2,kk-ll)
                     for ll in range(min(j-2,kk)+1))
        assert coef==catalan_binomial(j,kk),(j,kk)
print('PASS independent Narayana identity:',35*51,'coefficients')

# Exact finite path decomposition at first exit. Length includes all x/(1-x)
# contributions; the termination factor is then included as arbitrary padding.
@lru_cache(None)
def steps(L,q):
    return [(r,sum(B(ell,q,r) for ell in range(L))) for r in range(L)]
@lru_cache(None)
def walk(n,h,H=0):
    ans=1
    for L in range(1,n+1):
        for q in range(1,h+1):
            for r,mult in steps(L,q):
                hp=h+1-q+r
                if mult and (H==0 or hp<=H):ans+=mult*walk(n-L,hp,H)
    return ans
for H in range(1,5):
    unhit=[defaultdict(int) for _ in range(9)]
    hit=[defaultdict(int) for _ in range(9)]
    unhit[0][1]=1
    for n in range(9):
        for h,mult in list(unhit[n].items()):
            for L in range(1,9-n):
                for q in range(1,h+1):
                    for r,w in steps(L,q):
                        if w:
                            hp=h+1-q+r
                            (hit if hp>H else unhit)[n+L][hp]+=mult*w
    for n in range(9):
        decomposition=walk(n,1,H)+sum(mult*walk(n-m,h) for m in range(n+1) for h,mult in hit[m].items())
        assert decomposition==walk(n,1),(H,n)
print('PASS exact first-hit/suffix decomposition at 36 height/length pairs')
known=[1,1,2,5,14,42,133,442,1535,5546]
assert [1]+[walk(n-1,1) for n in range(1,10)]==known
print('PASS independent quadratic/jump walks reproduce a_0 through a_9')

# Numerical diagnostics only: fixed-tilt square-root convolution and supersolution.
mp.mp.dps=80
aval=mp.findroot(lambda a:7*a**3+14*a**2-7*a-1,mp.mpf('.51'))
num=lambda e:mp.mpf(str(s.N(e.subs(u,str(aval)),75)))
rr,zz,tt,ww,bb=map(num,[rho,zs,ts,Ws,b])
second=num(z2); constant=num(ss)
M=3000
sq=[mp.mpf(1)]
for n in range(1,M+1):sq.append(sq[-1]*(mp.mpf(n)-mp.mpf('1.5'))/n)
# H(w)=sqrt(1-zstar*w/z2)/(1-zstar*w) and sqrt(1-w).
analytic=[]
for n in range(M+1):
    analytic.append(sum(sq[j]*(zz/second)**j*zz**(n-j) for j in range(min(n,120)+1)))
for q in [20,100,500,1000,3000]:
    rootpart=sum(analytic[j]*sq[q-j] for j in range(min(q,120)+1))
    polynomialpart=(constant-(bb-rr*tt))*zz**q
    Aq=(polynomialpart-constant*rootpart)/(2*rr*tt)
    assert Aq>0
    print('DIAGNOSTIC q^(3/2) Q_q zstar^q:',q,mp.nstr(q**mp.mpf('1.5')*Aq,18))
for theta in [mp.mpf('.0001'),mp.mpf('.001'),mp.mpf('.01')]:
    xx=rr*mp.exp(-theta**2);zt=zz*mp.exp(-theta);tx=tt*mp.exp(theta)
    pole=1-xx*xx*tx*(1+ww)/(1-xx)**2
    Fmap=zt/(1-xx)*(1+xx*tx/(1-xx))*(1+ww)/pole
    mass=xx/(1-xx)*tx*(zt+xx*ww)/(1-zt)
    assert 0<Fmap<=ww and pole>0 and mass<1
    print('DIAGNOSTIC tilt supersolution:',mp.nstr(theta),mp.nstr(Fmap-ww,15),mp.nstr(mass,15))
print('ALL INDEPENDENT CHECKS PASSED')
