#!/usr/bin/env python3
"""Integer-only outward interval certificate for A116379 and A116380.
Python 3 standard library only. Run: python3 certify.py > certificate.json
No floating-point number occurs in the verification path.
"""
from fractions import Fraction as Q
from math import comb, factorial, isqrt
import hashlib, json
import argparse
from pathlib import Path

DIGITS=90
S=10**DIGITS
N=400
ORDER=6

class CertificationError(RuntimeError):
    pass

def require(condition,message='Certificate condition failed'):
    if not condition:
        raise CertificationError(message)

def ceildiv(a,b): return -((-a)//b)

class I:
    __slots__=('lo','hi')
    def __init__(self,x=0,hi=None,raw=False):
        if raw: self.lo,self.hi=x,hi
        elif isinstance(x,I): self.lo,self.hi=x.lo,x.hi
        else:
            q=Q(x); self.lo=q.numerator*S//q.denominator
            self.hi=ceildiv(q.numerator*S,q.denominator)
        require(self.lo <= self.hi)
    @staticmethod
    def endpoints(lo,hi):
        a,b=I(lo),I(hi); return I(a.lo,b.hi,raw=True)
    def __add__(a,b):
        b=I(b);return I(a.lo+b.lo,a.hi+b.hi,raw=True)
    __radd__=__add__
    def __neg__(a): return I(-a.hi,-a.lo,raw=True)
    def __sub__(a,b):return a+-I(b)
    def __rsub__(a,b):return I(b)+-a
    def __mul__(a,b):
        b=I(b); vals=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return I(min(vals)//S,ceildiv(max(vals),S),raw=True)
    __rmul__=__mul__
    def inv(a):
        require(a.lo * a.hi > 0, 'Interval division by zero')
        return I(S*S//a.hi,ceildiv(S*S,a.lo),raw=True)
    def __truediv__(a,b):return a*I(b).inv()
    def __rtruediv__(a,b):return I(b)*a.inv()
    def __pow__(a,n):
        require(n >= 0 and isinstance(n, int))
        p=I(1)
        while n:
            if n&1:p=p*a
            n//=2
            if n:a=a*a
        return p
    def sqrt(a):
        require(a.lo >= 0)
        l=isqrt(a.lo*S);h=isqrt(a.hi*S)
        if h*h<a.hi*S:h+=1
        return I(l,h,raw=True)
    def zero(a):return a.lo<=0<=a.hi
    def positive(a):return a.lo>0
    def negative(a):return a.hi<0
    def width(a):return Q(a.hi-a.lo,S)
    def json(a):return {'lo':fixed(a.lo),'hi':fixed(a.hi)}
    def outward(a,d=30):
        unit=10**(DIGITS-d)
        return [fixed(a.lo//unit*unit,d),fixed(ceildiv(a.hi,unit)*unit,d)]

def fixed(n,d=DIGITS):
    sign='-' if n<0 else ''; n=abs(n)
    return sign+str(n//S)+'.'+str(n%S).zfill(DIGITS)[:d]

def assert_lt(a,b):require(I(a).hi < I(b).lo, (I(a).json(), I(b).json()))

def log_iv(x,m=180):
    x=I(x);require(x.lo > 0)
    v=(x-1)/(x+1);r=max(abs(v.lo),abs(v.hi));require(r < S)
    r=I(r,r,raw=True)
    p=v;ans=I(0);v2=v*v
    for j in range(m):
        ans+=p/(2*j+1);p*=v2
    err=2*r**(2*m+1)/((2*m+1)*(1-r*r))
    return 2*ans+I(-err.hi,err.hi,raw=True)

def atan_bound(q,m):
    # Alternating-series enclosure, exactly rational before conversion to I.
    s=sum(((-1)**j*Q(1,(2*j+1)*q**(2*j+1)) for j in range(m)),Q(0))
    t=(-1)**m*Q(1,(2*m+1)*q**(2*m+1))
    return I.endpoints(min(s,s+t),max(s,s+t))

def pi_bound():return 16*atan_bound(5,80)-4*atan_bound(239,25)

def enumerate_subset(d,nmax):
    p=[[0]*(nmax+1) for _ in range(d+1)];p[0][0]=1
    a=[0]*(nmax+1)
    for n in range(1,nmax+1):
        a[n]=sum(p[j][n-1] for j in range(d+1))
        for deg in range(d,0,-1):
            for j in range(1,min(deg,nmax//n,a[n])+1):
                c=comb(a[n],j)
                for k in range(j*n,nmax+1):p[deg][k]+=c*p[deg-j][k-j*n]
    return a

def enumerate_newton(d,nmax):
    # Independent coefficientwise signed Newton recurrence.
    a=[0]*(nmax+1)
    e=[[0]*(nmax+1) for _ in range(d+1)];e[0][0]=1
    for m in range(nmax):
        if m:
            for j in range(1,d+1):
                val=sum((-1)**(k-1)*a[n]*e[j-k][m-k*n]
                        for k in range(1,j+1) for n in range(1,m//k+1))
                require(val % j == 0)
                e[j][m]=val//j
        a[m+1]=sum(e[j][m] for j in range(d+1))
    return a

def inner(a,rho,k,j):
    # Tk,j = sum a[n] rho^(kn) binom(kn,j), with nonnegative tail.
    w=rho**k; val=I(0)
    for n in range(len(a)-1,-1,-1):val=val*w+a[n]*comb(k*n,j)
    q=I(4)*I(w.hi,w.hi,raw=True)
    # a[n]<=4^(n-1), binom(kn,j)<=(kn)^j/j!.
    ratio=q*I(Q(N+2,N+1))**j
    assert_lt(ratio,1)
    tail=(I(k**j*(N+1)**j)*q**(N+1))/(4*factorial(j)*(1-ratio))
    val=val+I(0,tail.hi,raw=True)
    return val,tail

def elementary(rho,y,inners,d):
    p=[None,y]+[inners[k] for k in range(2,d+1)]
    e=[I(1)]
    for j in range(1,d+1):e.append(sum(((-1)**(k-1)*p[k]*e[j-k] for k in range(1,j+1)),I(0))/j)
    return e

def values(rho,y,inners,d):
    e=elementary(rho,y,inners,d)
    return rho*sum(e,I(0))-y,rho*sum(e[:-1],I(0))-1

def critical_y(rho,inners,d,tol=Q(1,10**60)):
    # Holds every positive solution of Gy=1 for every z in rho.
    lo,hi=0,2*S
    require(values(rho, I(lo, lo, raw=True), inners, d)[1].negative())
    require(values(rho, I(hi, hi, raw=True), inners, d)[1].positive())
    while Q(hi-lo,S)>tol:
        mid=(lo+hi)//2;v=values(rho,I(mid,mid,raw=True),inners,d)[1]
        if v.negative():lo=mid
        elif v.positive():hi=mid
        else:break
    return I(lo,hi,raw=True)

# Bivariate polynomials: keys (power of t,power of h), degree t+h<=ORDER.
def padd(a,b):
    out=dict(a)
    for key,val in b.items():out[key]=out.get(key,I(0))+val
    return out

def pscale(a,c):return {key:val*c for key,val in a.items()}

def pmul(a,b):
    out={}
    for (i,j),v in a.items():
        for (k,l),w in b.items():
            if i+j+k+l<=ORDER:
                key=(i+k,j+l);out[key]=out.get(key,I(0))+v*w
    return out

def jet_F(a,rho,tau,d):
    z={(0,0):rho,(2,0):-rho};p=[None,{(0,0):tau,(0,1):I(1)}];tails={}
    for k in range(2,d+1):
        poly={}
        for j in range(ORDER//2+1):
            val,tail=inner(a,rho,k,j);poly[(2*j,0)]=(-1)**j*val
            tails[f'{k},{j}']=tail
        p.append(poly)
    e=[{(0,0):I(1)}]
    for j in range(1,d+1):
        poly={}
        for k in range(1,j+1):poly=padd(poly,pscale(pmul(p[k],e[j-k]),(-1)**(k-1)))
        e.append(pscale(poly,I(1)/j))
    phi={}
    for poly in e:phi=padd(phi,poly)
    f=pmul(z,phi)
    f[(0,0)]-=tau;f[(0,1)]-=1
    residuals={'F':f[(0,0)],'Fy':f[(0,1)]}
    require(all((v.zero() for v in residuals.values())))
    # Exact characteristic identities, not a numerical near-zero assumption.
    f[(0,0)]=I(0);f[(0,1)]=I(0)
    return f,tails,residuals

def umul(a,b):
    c=[I(0)]*(ORDER+1)
    for i,v in enumerate(a):
        for j,w in enumerate(b[:ORDER+1-i]):c[i+j]=c[i+j]+v*w
    return c

def substitute(f,aa):
    h=[I(0)]*(ORDER+1)
    for i,v in enumerate(aa,1):h[i]=v
    hp=[[I(1)]+[I(0)]*ORDER]
    for q in range(1,5):hp.append(umul(hp[-1],h))
    ans=[I(0)]*(ORDER+1)
    for (p,q),v in f.items():
        for j in range(ORDER+1-p):ans[p+j]=ans[p+j]+v*hp[q][j]
    return ans

def branch_bounds():
    z=I(Q(9,20));a2=(1-(1-4*z**2).sqrt())/2;u=z**2/(1-4*z**2).sqrt()
    a4=(1-(1-4*z**4).sqrt())/2;v=z**4/(1-4*z**4).sqrt()
    assert_lt(a2,Q(283,1000));assert_lt(u,Q(465,1000))
    assert_lt(a4,Q(44,1000));assert_lt(v,Q(45,1000))
    A2,U,A4,V=map(Q,['.283','.465','.044','.045'])
    lower=[1-A2/2-A4/4-U-V,1-A2/2-U,Q(1,2)-A2/4-U/2]
    require(all((x > 0 for x in lower)))
    require(Q(9, 20) * (1 + A2 / 3) < 1)
    return {'Catalan_A2':a2,'Catalan_u':u,'Catalan_A4':a4,'Catalan_v':v,
            'd4_Gz_polynomial_lower':[str(x) for x in lower]}

# Locator guesses only. EVERY endpoint is independently certified below.
RHO_LO={3:Q('0.400774500477539473704620732219347400763189247'),
        4:Q('0.397585196670872770885924531229552609191269805')}

def certify(d,pi,coefficients_out=None):
    a=enumerate_subset(d,N)
    require(a == enumerate_newton(d, N))
    require(all((1 <= a[n] <= comb(2 * n - 2, n - 1) // n for n in range(1, N + 1))))
    require(all((a[n] <= a[n + 1] for n in range(1, N))))
    if coefficients_out is not None:
        target=Path(coefficients_out)/f'a_d{d}_through_{N}.json'
        # Explicit opt-in export only; existing files are never overwritten.
        with target.open('x') as handle:handle.write(json.dumps(a)+'\n')
    rootlo=RHO_LO[d];roothi=rootlo+Q(1,10**45)
    endpoint=[]
    for x in (rootlo,roothi):
        z=I(x);inners={k:inner(a,z,k,0)[0] for k in range(2,d+1)}
        yc=critical_y(z,inners,d)
        minimum=values(z,yc,inners,d)[0]
        endpoint.append({'z':z,'ycrit':yc,'minimum_F':minimum})
    require(endpoint[0]['minimum_F'].negative())
    require(endpoint[1]['minimum_F'].positive())
    rho=I.endpoints(rootlo,roothi)
    inners={k:inner(a,rho,k,0)[0] for k in range(2,d+1)}
    tau=critical_y(rho,inners,d)
    require(tau.width() < Q(1, 10 ** 42))
    f,tails,residuals=jet_F(a,rho,tau,d)
    require(f[2, 0].negative() and f[0, 2].positive())
    aa=[-(-f[(2,0)]/f[(0,2)]).sqrt()]
    denom=2*f[(0,2)]*aa[0]
    for m in range(2,6):
        rem=substitute(f,aa)[m+1]
        aa.append(-rem/denom)
    # Necessary residual check through t^6, with all solved coefficients.
    require(all((v.zero() for v in substitute(f, aa)[2:])))
    C=-aa[0]/(2*pi.sqrt())
    c1=I(Q(3,8))-I(Q(3,2))*aa[2]/aa[0]
    c2=I(Q(25,128))-I(Q(45,16))*aa[2]/aa[0]+I(Q(15,4))*aa[4]/aa[0]
    lam=-log_iv(rho);b=-I(Q(3,2))*log_iv(lam)-log_iv(C)
    out={'d':d,'oeis':'A116379' if d==3 else 'A116380','rho':rho,'tau':tau,
         'Gz':-f[(2,0)]/rho,'Gyy':2*f[(0,2)],'C':C,'c1':c1,'c2':c2,
         'lambda':lam,'inverse_b':b,'puiseux':{f'a{i}':v for i,v in enumerate(aa,1)},
         'endpoint_sign_certificates':endpoint,'characteristic_box_residuals':residuals,
         'bivariate_F_jet':{f'{i},{j}':v for (i,j),v in sorted(f.items())},
         'inner_tail_bounds':tails,'initial_30':a[1:31],
         'coefficient_sha256':hashlib.sha256((json.dumps(a)+'\n').encode()).hexdigest(),
         'two_enumerations_agree':True,'Catalan_bound_checked_through_N':True}
    out['readable_enclosures']={key:out[key].outward(30) for key in ['rho','tau','C','c1','c2','lambda','inverse_b']}
    require(all((out[key].width() < Q(1, 10 ** 35) for key in ['rho', 'tau', 'C', 'c1', 'c2'])))
    return out

def encode(obj):
    if isinstance(obj,I):return obj.json()
    raise TypeError(type(obj))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients-out',type=Path,help='Existing directory for opt-in coefficient exports; refuses to overwrite files')
    args=parser.parse_args()
    branch=branch_bounds();pi=pi_bound()
    assert_lt(3,pi);assert_lt(pi,Q(22,7))
    output={'method':'exact integer fixed-denominator outward intervals; no floating point',
            'scale':str(S),'decimal_precision':DIGITS,'enumeration_N':N,
            'pi':pi,'global_branch_bounds':branch,'cases':[certify(d,pi,args.coefficients_out) for d in [3,4]]}
    print(json.dumps(output,default=encode,indent=2))
