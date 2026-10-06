"""Independent exact arithmetic for class1509; imported by check.py."""
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
from math import isqrt
from check import (need,keys,interval,add,mul,scale,div,shift,monomial,padd,pmul,ps,
                   displayed_interval,atan_interval,sha256,json)

class RF:
    def __init__(self,a,b=None):
        self.a=a if type(a) is dict else {(0,0):F(a)}
        self.b={(0,0):F(1)} if b is None else b
    def __add__(self,other):
        o=rf(other);return RF(padd(pmul(self.a,o.b),pmul(o.a,self.b)),pmul(self.b,o.b))
    __radd__=__add__
    def __neg__(self):return RF(ps(self.a,-1),self.b)
    def __sub__(self,o):return self+-rf(o)
    def __rsub__(self,o):return rf(o)+-self
    def __mul__(self,other):
        o=rf(other);return RF(pmul(self.a,o.a),pmul(self.b,o.b))
    __rmul__=__mul__
    def __truediv__(self,other):
        o=rf(other);need(bool(o.a),'COMPANION_SYMBOLIC_ZERO_DIVISOR');return RF(pmul(self.a,o.b),pmul(self.b,o.a))
    def __rtruediv__(self,o):return rf(o)/self
    def __pow__(self,n):
        out=RF(1)
        for _ in range(n):out=out*self
        return out
    def zero(self):return not self.a or all(v==0 for v in self.a.values())
def rf(x):return x if isinstance(x,RF) else RF(x)

def scalar_algebra():
    z=RF({(1,0):F(1)});x=RF({(0,1):F(1)});y=z*x/(1-z*x)
    K=1-x+z*x+z*x*x
    c=(2*z*x-1)*K/(z*(x-1))
    d=(2*z*x-1)*(z*x+z-1)/(z*(z*x-1))
    e=-2*x*(z*x+z-1)/(x-1)
    A=z*x*z*x/(1-x)+z*x*y/((1-x)*(1-y))+z*x*y/((1-y)*(x-y))*e
    H=-z*x*(1+z*x*x/(1-x))-z*x*y/((1-x)*(x-y))+z*x*y/((1-y)*(x-y))*c
    B=z*x+z*x*y/((1-y)*(x-y))*d
    need(A.zero() and H.zero() and B.zero(),'COMPANION_SCALAR_IDENTITY')
    p=z*(1-x)/((1-2*z*x)*K)
    q=(1-x)*(1-z-z*x)/((1-z*x)*K)
    r=2*z*x*(1-z-z*x)/((1-2*z*x)*K)
    need((p*c-1).zero() and (p*d+q).zero() and (p*e+r).zero(),'COMPANION_REVERSE_IDENTITY')
    z=(x-1)/(x*(x+1));y=(x-1)/2
    d=(2*z*x-1)*(z*x+z-1)/(z*(z*x-1));e=-2*x*(z*x+z-1)/(x-1)
    need((1-x+z*x+z*x*x).zero() and (d-y+1/y).zero() and (e-1/y).zero(),'COMPANION_ROOT_IDENTITY')
    return 'exact cleared rational-function identities, including source reduction and root specialization'

def state_terms(N):
    states={(0,0):1};out=[]
    for n in range(N+1):
        out.append(sum(v for (p,s),v in states.items() if s<=1))
        nxt=defaultdict(int)
        for (p,s),v in states.items():
            nxt[p+1,s]+=v
            if s:nxt[p+1,s-1]+=v
            if s<=1:
                for k in range(1,p+1):nxt[k,0]+=v
                for k in range(1,p):
                    for t in range(1,p-k+1):nxt[k,t]+=v
        states=nxt
    return out

def orbit_terms(N):
    D=N+2;one=monomial(D);z=monomial(D,1)
    X=[0]*D;X[0]=1
    for n in range(1,D):X[n]=X[n-1]+sum(X[j]*X[n-1-j] for j in range(n))
    y=scale(add(X,scale(one,-1)),F(1,2));x=y
    U=[0]*D;V=[0]*D;P=one
    for j in range(N+1):
        zx=shift(x);K=add(add(add(one,scale(x,-1)),zx),shift(mul(x,x)))
        p=div(shift(add(one,scale(x,-1))),mul(add(one,scale(zx,-2)),K))
        q=div(mul(add(one,scale(x,-1)),add(add(one,scale(z,-1)),scale(zx,-1))),mul(add(one,scale(zx,-1)),K))
        r=div(mul(scale(zx,2),add(add(one,scale(z,-1)),scale(zx,-1))),mul(add(one,scale(zx,-2)),K))
        U=add(U,mul(P,q));V=add(V,mul(P,r));P=mul(P,p)
        x=div(zx,add(one,scale(zx,-1)))
    A=div(add(add(one,scale(mul(y,y),-1)),mul(y,U)),add(one,scale(mul(y,V),-1)))
    need(all(F(v).denominator==1 for v in A),'COMPANION_ORBIT_INTEGRAL')
    return [int(v) for v in A[:N+1]]

def brute_terms(N):
    out=[]
    for n in range(N+1):
        count=0
        for seq in product(*(range(i) for i in range(1,n+1))):
            valid=True
            for k in range(n):
                earlier_larger=False
                for j in range(k):
                    if earlier_larger and seq[j]>=seq[k]:valid=False;break
                    earlier_larger=earlier_larger or seq[j]>seq[k]
                if not valid:break
            count+=valid
        out.append(count)
    return out

# Fixed-denominator intervals, independently implemented with rational rounding.
S=10**60
class Interval:
    def __init__(self,lo,hi=None):
        if isinstance(lo,Interval):self.lo,self.hi=lo.lo,lo.hi;return
        lo=F(lo);hi=lo if hi is None else F(hi)
        need(lo<=hi,'COMPANION_INTERVAL_ORDER')
        self.lo=F(lo.numerator*S//lo.denominator,S)
        self.hi=F(-((-hi.numerator*S)//hi.denominator),S)
    def __add__(self,o):
        o=iv(o);return Interval(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return Interval(-self.hi,-self.lo)
    def __sub__(self,o):return self+-iv(o)
    def __rsub__(self,o):return iv(o)+-self
    def __mul__(self,o):
        o=iv(o);v=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi];return Interval(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=iv(o);need(not o.lo<=0<=o.hi,'COMPANION_INTERVAL_ZERO_DIVISOR')
        return self*Interval(1/o.hi,1/o.lo)
    def __rtruediv__(self,o):return iv(o)/self
    def sqrt(self):
        need(self.lo>=0,'COMPANION_NEGATIVE_SQRT')
        low=isqrt(self.lo.numerator*S*S//self.lo.denominator)
        high=isqrt(self.hi.numerator*S*S//self.hi.denominator)+1
        return Interval(F(low,S),F(high,S))
    def widen(self,error):return self+Interval(-error,error)
def iv(x):return x if isinstance(x,Interval) else Interval(x)

class Dual:
    def __init__(self,value,derivative=0):self.value,self.derivative=iv(value),iv(derivative)
    def __add__(self,o):
        o=dual(o);return Dual(self.value+o.value,self.derivative+o.derivative)
    __radd__=__add__
    def __neg__(self):return Dual(-self.value,-self.derivative)
    def __sub__(self,o):return self+-dual(o)
    def __rsub__(self,o):return dual(o)+-self
    def __mul__(self,o):
        o=dual(o);return Dual(self.value*o.value,self.derivative*o.value+self.value*o.derivative)
    __rmul__=__mul__
    def __truediv__(self,o):
        o=dual(o);return Dual(self.value/o.value,(self.derivative*o.value-self.value*o.derivative)/(o.value*o.value))
    def __rtruediv__(self,o):return dual(o)/self
def dual(x):return x if isinstance(x,Dual) else Dual(x)

PARAMS={'coefficient_n_max':80,'external_prefix_n_max':25,'brute_n_max':8,
 'interval_N':24,'interval_places':60,'derivative_places':16,'C_places':16,
 'tail_value_numerator':40,'tail_value_denominator':3,'derivative_tail_factor':1000}
PROVENANCE={'sequence':'A279567','class':1509,'offset':0,'oeis_url':'https://oeis.org/A279567',
 'paper_url':'https://arxiv.org/html/2512.21943v3','paper_sections':'3.6 equations (3.34)-(3.37); 4.2 equation (4.10)',
 'retrieved_date':'2026-10-02','prefix_scope':'26 displayed OEIS terms n=0..25; n=26..80 are internal cross-checks'}

def validate_fixture(f):
    keys(f,['provenance','parameters','external_prefix','internal_terms','F_derivative','C','refined'],'COMPANION_SCHEMA')
    for key,expected in [('provenance',PROVENANCE),('parameters',PARAMS)]:
        keys(f[key],expected,'COMPANION_'+key.upper()+'_SCHEMA')
        for name,value in expected.items():
            need(type(f[key][name]) is type(value) and f[key][name]==value,'COMPANION_'+key.upper()+'_'+name.upper())
    for key,length in [('external_prefix',26),('internal_terms',81)]:
        need(type(f[key]) is list and len(f[key])==length,'COMPANION_SEQUENCE_LENGTH')
        need(all(type(v) is int and 0<v<10**100 for v in f[key]),'COMPANION_SEQUENCE_INTEGER')
    interval(f['F_derivative'],16,'COMPANION_ENCLOSURE_VALUE');interval(f['C'],16,'COMPANION_ENCLOSURE_VALUE')
    keys(f['refined'],['parameters','C','c1','c2'],'COMPANION_REFINED_SCHEMA')
    keys(f['refined']['parameters'],REFINED_PARAMS,'COMPANION_REFINED_PARAMETER_SCHEMA')
    for name,value in REFINED_PARAMS.items():
        need(type(f['refined']['parameters'][name]) is int and f['refined']['parameters'][name]==value,'COMPANION_REFINED_PARAMETER_'+name.upper())
    for key,places in [('C',33),('c1',31),('c2',29)]:interval(f['refined'][key],places,'COMPANION_REFINED_ENCLOSURE_VALUE')

def denominator_bounds():
    R=F(43,250);X=F(483,200);Y=F(177,250);w=F(7,50)
    a=R/(1-R*X);K=(1-a)*(1-R*X*Y)
    need(0<a<1 and K>0,'COMPANION_FIRST_DENOMINATORS')
    need(R*(1+Y)/((1-2*R*Y)*K)<F(4,5),'COMPANION_FIRST_P')
    need(2*R*Y*(1+R+R*Y)/((1-2*R*Y)*K)<F(17,20),'COMPANION_FIRST_R')
    need(R*Y/(1-R*Y)<w,'COMPANION_FIRST_ORBIT')
    Ksmall=1-w-R*w-R*w*w
    need(Ksmall>0 and 1-2*R*w>0,'COMPANION_TAIL_DENOMINATORS')
    need(R*(1+w)/((1-2*R*w)*Ksmall)<F(1,4),'COMPANION_TAIL_P')
    need(2*R*(1+R+R*w)/((1-2*R*w)*Ksmall)<F(3,5),'COMPANION_TAIL_R')
    need(R/(1-R*w)<F(9,50),'COMPANION_TAIL_ORBIT')
    need((1+w)*(1+R+R*w)/((1-R*w)*Ksmall)<2,'COMPANION_TAIL_Q')
    bound=Y*(F(17,20)+F(4,5)*(F(3,5)*w)/(1-F(1,4)*F(9,50)))
    need(bound<F(2,3),'COMPANION_GLOBAL_DENOMINATOR')
    Yc=F(709,1000);Kc=1-Yc-R*Yc-R*Yc*Yc
    need(Kc>0 and R*(1+Yc)/((1-2*R*Yc)*Kc)<5 and R*Yc/(1-R*Yc)<w,'COMPANION_CAUCHY_DISK')
    return bound

def amplitude(f):
    bound=denominator_bounds()
    sqrt2=Interval(2).sqrt();rho=3-2*sqrt2;y=sqrt2/2
    need(F(171,1000)<rho.lo<rho.hi<F(43,250) and F(707,1000)<y.lo<y.hi<F(177,250),'COMPANION_CRITICAL_POINT')
    z=Dual(rho);x=Dual(y,1);points=[]
    for _ in range(24):points.append(x);x=z*x/(1-z*x)
    U=Dual(0);V=Dual(0)
    for x in reversed(points):
        K=1-x+z*x+z*x*x
        p=z*(1-x)/((1-2*z*x)*K)
        q=(1-x)*(1-z-z*x)/((1-z*x)*K)
        r=2*z*x*(1-z-z*x)/((1-2*z*x)*K)
        U=q+p*U;V=r+p*V
    E=F(40,3*4**23)
    U=Dual(U.value.widen(E),U.derivative.widen(1000*E));V=Dual(V.value.widen(E),V.derivative.widen(1000*E))
    x=Dual(y,1);value=(1-x*x+x*U)/(1-x*V)
    d=value.derivative
    need(d.lo>0,'COMPANION_DERIVATIVE_POSITIVE')
    need(F(f['F_derivative']['lower'])<d.lo and d.hi<F(f['F_derivative']['upper']),'COMPANION_DERIVATIVE_ENCLOSURE')
    a=atan_interval(5,60);b=atan_interval(239,20)
    pi=16*Interval(*a)-4*Interval(*b)
    kappa=(1-rho*rho).sqrt()/(4*rho)
    C=kappa*d/(2*pi.sqrt())
    need(0<F(f['C']['lower'])<C.lo and C.hi<F(f['C']['upper']),'COMPANION_C_ENCLOSURE')
    return {'global_yV_bound':str(bound),'global_yV_strict_upper':'2/3','interval_N':24,
            'value_tail':str(E),'derivative_tail':str(1000*E),
            'F_derivative':displayed_interval((d.lo,d.hi),16),'C':displayed_interval((C.lo,C.hi),16)}

def run(f):
    validate_fixture(f)
    algebra=scalar_algebra()
    terms=state_terms(80)
    need(terms==f['internal_terms'],'COMPANION_INTERNAL_TERMS')
    need(terms[:26]==f['external_prefix'],'COMPANION_EXTERNAL_PREFIX')
    need(orbit_terms(80)==terms,'COMPANION_ORBIT_STATE_AGREEMENT')
    need(brute_terms(8)==terms[:9],'COMPANION_BRUTE_STATE_AGREEMENT')
    need(all(terms[n+1]>terms[n] for n in range(1,80)),'COMPANION_FINITE_MONOTONICITY')
    certificate=amplitude(f)
    refined_certificate=refined(f)
    return {'algebra':algebra,'internal_n_range':[0,80],'internal_coefficients':81,
            'external_prefix_n_range':[0,25],'external_terms':26,'brute_n_range':[0,8],
            'terms_sha256':sha256(json.dumps(terms,separators=(',',':')).encode()).hexdigest(),
            'certificate':certificate,'refined_certificate':refined_certificate}

# Degree-five directed interval jets. The square root is reconstructed by solving
# J(t)^2=1-rho^2+rho^2 t^2 coefficientwise, independently of the displayed formula.
class Jet:
    degree=5
    def __init__(self,values=0):
        vals=values if type(values) is list else [values]
        self.a=[iv(v) for v in vals]+[iv(0)]*(6-len(vals))
        need(len(self.a)==6,'COMPANION_JET_DEGREE')
    def __add__(self,o):
        o=jet(o);return Jet([a+b for a,b in zip(self.a,o.a)])
    __radd__=__add__
    def __neg__(self):return Jet([-a for a in self.a])
    def __sub__(self,o):return self+-jet(o)
    def __rsub__(self,o):return jet(o)+-self
    def __mul__(self,o):
        o=jet(o);return Jet([sum((self.a[k]*o.a[n-k] for k in range(n+1)),iv(0)) for n in range(6)])
    __rmul__=__mul__
    def inverse(self):
        b=[1/self.a[0]]
        for n in range(1,6):b.append(-sum((self.a[j]*b[n-j] for j in range(1,n+1)),iv(0))/self.a[0])
        return Jet(b)
    def __truediv__(self,o):return self*jet(o).inverse()
    def __rtruediv__(self,o):return jet(o)*self.inverse()
def jet(x):return x if isinstance(x,Jet) else Jet(x)

REFINED_PARAMS={'N':96,'degree':5,'circle_denominator':10000,'tail_numerator':32,
 'tail_denominator':15,'quotient_tail_factor':100,'C_places':33,'c1_places':31,'c2_places':29}

def refined(f):
    sqrt2=Interval(2).sqrt();rho=3-2*sqrt2;y0=sqrt2/2
    h=F(1,10000);R=F(43,250);X=F(483,200);Y=F(177,250)
    need(F(171,1000)<rho.lo<rho.hi<F(171573,10**6),'COMPANION_REFINED_RHO')
    need(F(707106,10**6)<y0.lo<y0.hi<F(707107,10**6),'COMPANION_REFINED_Y')
    change=(h*h+h)/(4*F(171,1000)*(1-h*h))
    need(F(171573,10**6)*(1+h*h)<R and change<F(1,5000),'COMPANION_T_CIRCLE')
    need(F(707107,10**6)+change<Y and 1+2*(F(707107,10**6)+change)<X,'COMPANION_BOTH_BRANCH_BOX')
    q0=(1+Y)*(1+R+R*Y)/((1-R*Y)*(1-R/(1-R*X))*(1-R*X*Y))
    need(q0+F(4,5)*F(8,3)<8 and 1+Y*Y+8*Y<8,'COMPANION_QUOTIENT_NUMERATOR')
    E=F(32,15*4**95)
    need(Y*E<F(1,12) and 4*Y+8*Y*12<100,'COMPANION_QUOTIENT_TAIL')
    z=Jet([rho,0,-rho]);t=Jet([0,1])
    rad=[1-rho*rho,iv(0),rho*rho,iv(0),iv(0),iv(0)]
    root=[rad[0].sqrt()]
    for n in range(1,6):root.append((rad[n]-sum((root[j]*root[n-j] for j in range(1,n)),iv(0)))/(2*root[0]))
    y=(1-3*z-t*Jet(root))/(4*z)
    x=y;points=[]
    for _ in range(96):points.append(x);x=z*x/(1-z*x)
    U=Jet(0);V=Jet(0)
    for x in reversed(points):
        K=1-x+z*x+z*x*x
        p=z*(1-x)/((1-2*z*x)*K)
        q=(1-x)*(1-z-z*x)/((1-z*x)*K)
        r=2*z*x*(1-z-z*x)/((1-2*z*x)*K)
        U=q+p*U;V=r+p*V
    H=(1-y*y+y*U)/(1-y*V)
    b=[v.widen(100*E/h**j) for j,v in enumerate(H.a)]
    need(b[1].hi<0,'COMPANION_B1_NONZERO')
    a=atan_interval(5,60);pi_b=atan_interval(239,20)
    pi=16*Interval(*a)-4*Interval(*pi_b)
    C=-b[1]/(2*pi.sqrt())
    c1=F(3,8)-F(3,2)*b[3]/b[1]
    c2=F(25,128)-F(45,16)*b[3]/b[1]+F(15,4)*b[5]/b[1]
    result={}
    for key,v,places in [('C',C,33),('c1',c1,31),('c2',c2,29)]:
        result[key]=displayed_interval((v.lo,v.hi),places)
        need(result[key]==f['refined'][key],'COMPANION_REFINED_'+key.upper())
    result.update({'N':96,'degree':5,'circle_radius':'1/10000','UV_tail':str(E),
                   'quotient_tail':str(100*E),'b1_strictly_negative':True})
    return result
