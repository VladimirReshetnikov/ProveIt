"""Independently reconstructed rational mathematics for report119.
No floating-point number is used. Analytic tail inequalities are supplied by the
report; this module verifies their exact arithmetic, not the analytic theorems.
"""
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import comb, isqrt
import json
from support import need

# Dense truncated power-series arithmetic, over rationals or polynomial rings.
def add(a,b): return [x+y for x,y in zip(a,b)]
def scale(a,c): return [x*c for x in a]
def mul(a,b):
    out=[0]*len(a)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:len(a)-i]):
                if y:out[i+j]+=x*y
    return out

def inv(a):
    need(a[0]!=0,'SERIES_ZERO_DIVISOR')
    out=[F(1)/a[0]]
    for k in range(1,len(a)):
        out.append(-sum(a[j]*out[k-j] for j in range(1,k+1))/a[0])
    return out

def div(a,b):return mul(a,inv(b))
def unit(n,c=1):return [c]+[0]*(n-1)
def shift(a,k):return [0]*k+a[:len(a)-k]
def power(a,n):
    out=unit(len(a))
    for _ in range(n):out=mul(out,a)
    return out

def binomial(a,k):
    out=F(1)
    for j in range(k):out=out*(a-j)/(j+1)
    return out

# Sparse multivariate Laurent polynomials; equality means exact coefficient equality.
class P:
    dimensions=5
    def __init__(self,value=0):
        self.p=value if type(value) is dict else ({(0,)*self.dimensions:F(value)} if value else {})
        self.p={k:F(v) for k,v in self.p.items() if v}
    @classmethod
    def variable(cls,j):
        a=[0]*cls.dimensions;a[j]=1;return cls({tuple(a):1})
    def __add__(self,other):
        other=pol(other);out=defaultdict(F,self.p)
        for k,v in other.p.items():out[k]+=v
        return P(dict(out))
    __radd__=__add__
    def __neg__(self):return P({k:-v for k,v in self.p.items()})
    def __sub__(self,other):return self+-pol(other)
    def __rsub__(self,other):return pol(other)+-self
    def __mul__(self,other):
        other=pol(other);out=defaultdict(F)
        for k,x in self.p.items():
            for l,y in other.p.items():out[tuple(i+j for i,j in zip(k,l))]+=x*y
        return P(dict(out))
    __rmul__=__mul__
    def __pow__(self,n):
        if n<0:
            need(len(self.p)==1,'POLYNOMIAL_NEGATIVE_POWER')
            k,v=next(iter(self.p.items()));return P({tuple(j*n for j in k):v**n})
        out=P(1)
        for _ in range(n):out=out*self
        return out
    def __eq__(self,other):return self.p==pol(other).p
    def __bool__(self):return bool(self.p)
def pol(x):return x if isinstance(x,P) else P(x)

class RF:
    def __init__(self,n,d=1):self.n,self.d=pol(n),pol(d)
    def __add__(self,other):
        other=rf(other);return RF(self.n*other.d+other.n*self.d,self.d*other.d)
    __radd__=__add__
    def __neg__(self):return RF(-self.n,self.d)
    def __sub__(self,other):return self+-rf(other)
    def __rsub__(self,other):return rf(other)+-self
    def __mul__(self,other):
        other=rf(other);return RF(self.n*other.n,self.d*other.d)
    __rmul__=__mul__
    def __truediv__(self,other):
        other=rf(other);need(bool(other.n),'RATIONAL_FUNCTION_ZERO_DIVISOR')
        return RF(self.n*other.d,self.d*other.n)
    def __rtruediv__(self,other):return rf(other)/self
    def __pow__(self,n):
        if n<0:return RF(self.d**(-n),self.n**(-n))
        return RF(self.n**n,self.d**n)
    def __eq__(self,other):
        other=rf(other);return self.n*other.d==other.n*self.d
def rf(x):return x if isinstance(x,RF) else RF(x)

def algebra():
    z,x,y=map(lambda j:RF(P.variable(j)),range(3))
    f=1/(1-z*x)
    K=(x-1)**2-z*x**3
    c=K/(1-x);d=x-f;e=1+z*x*x/(1-x)
    need(1-f+z*x*f==0,'FIRST_KERNEL_SUBSTITUTION')
    need((x*x+f-2*x*f)/(f*(1-x))==c,'SOURCE_SCALAR_C')
    need(-(1-f)*(x-f)/(z*x*f)==d,'SOURCE_SCALAR_D')
    need(-(x-f)/(f*(1-x))==e,'SOURCE_SCALAR_E')
    need(c==1-x*e,'CANCELED_C_IDENTITY')
    # Impose K=0 by parametrizing z=(x-1)^2/x^3. No root approximation.
    zk=(x-1)**2/x**3;Y=1/(1-zk*x)
    need(Y==x*x/(2*x-1),'SECOND_KERNEL_Y')
    need(1+zk*x*x/(1-x)==1/x,'SECOND_KERNEL_E')
    need((x-1)**2-zk*x**3==0,'SECOND_KERNEL_ZERO')
    # Orbit cancellation holds with arbitrary predecessor y and x=f_z(y).
    xx=1/(1-z*y)
    need(xx-1==z*y*xx,'ORBIT_DIFFERENCE_IDENTITY')
    need(1+z*xx*xx/(1-xx)==1-xx/y,'ORBIT_E_CANCELLATION')
    # Verify discriminant/resultant factor via explicit elimination K_x.
    need(2*(x-1)-3*((x-1)**2/x**3)*x*x==(x-1)*(3-x)/x,'CRITICAL_ELIMINATION')
    rho=F(4,27)
    for center in [F(3),F(3,4)]:
        need((center-1)**2-rho*center**3==0,'CRITICAL_ROOT_VALUE')
    need(2*(3-1)-3*rho*3**2==0,'CRITICAL_DOUBLE_ROOT')
    need(2*(F(3,4)-1)-3*rho*F(3,4)**2!=0,'LOWER_ROOT_REGULAR')
    need((2-6*rho*3)*F(12,2)+rho*3**3==0,'CRITICAL_SQRT_SLOPE')
    # Laurent-polynomial inversion identities in lambda,p,ell1,ell2,ell3.
    lam,p,l1,l2,l3=(P.variable(j) for j in range(5))
    eta1=-l1*lam**(-1)
    eta2=-p*l1*lam**(-2)-l2*lam**(-1)
    eta3=-p*p*l1*lam**(-3)-p*l2*lam**(-2)-l1*l1*lam**(-2)-l3*lam**(-1)
    for j,res in enumerate([lam*eta1+l1,lam*eta2-p*eta1+l2,
                            lam*eta3-p*eta2-l1*eta1+l3],1):
        need(res==0,'INVERSE_ETA'+str(j))
    # log(1+d1 h+d2 h^2+d3 h^3), exact coefficient identities.
    d1,d2,d3=(P.variable(j) for j in range(3))
    v=[P(0),d1,d2,d3]
    logv=add(add(v,scale(mul(v,v),F(-1,2))),scale(power(v,3),F(1,3)))
    need(logv[1:]==[d1,d2-d1*d1*F(1,2),d3-d1*d2+d1**3*F(1,3)],'LOG_CORRECTION_ALGEBRA')
    # First log-log correction: residual at L^-1 is D-p B+lambda d1.
    lam,p,B,d1=(P.variable(j) for j in range(4));D=p*B-lam*d1
    need(D-p*B+lam*d1==0,'LOGLOG_INVERSE_ALGEBRA')
    return {'source_scalar':'three exact rational identities',
            'root_and_cancellation':'exact identities and critical elimination',
            'inverse':'eta1, eta2, eta3 and log-log residuals vanish'}

def tree(N):
    states={(0,0):1};terms=[];hist=[]
    for n in range(N+1):
        terms.append(sum(states.values()));hist.append(states)
        if n==N:break
        nxt=defaultdict(int)
        # Independently aggregate successors of type two by p, since s disappears.
        marginal=defaultdict(int)
        for (p,s),count in states.items():
            marginal[p]+=count
            for k in range(s+1):nxt[p+1,k]+=count
        for p,count in marginal.items():
            for newp in range(1,p+1):
                for k in range(p+1-newp):nxt[newp,k]+=count
        states=dict(nxt)
    return terms,hist

def brute(N):
    out=[]
    for n in range(N+1):
        good=0
        for seq in product(*(range(k) for k in range(1,n+1))):
            # A triple exists iff at least two earlier entries exceed seq[k].
            if all(sum(v>seq[k] for v in seq[:k])<2 for k in range(n)):good+=1
        out.append(good)
    return out

def source_series(hist,N):
    for x,y in [(F(2,3),F(7,5)),(F(5,4),F(3,7))]:
        B=[sum(v*x**p*y**s for (p,s),v in h.items()) for h in hist[:N+1]]
        Hx=[sum(v*x**p for (p,s),v in h.items()) for h in hist[:N+1]]
        Hy=[sum(v*y**p for (p,s),v in h.items()) for h in hist[:N+1]]
        A=[sum(h.values()) for h in hist[:N+1]]
        den=(1-x)*(x-y)*(1-y)
        for n in range(N+1):
            rhs=den if n==0 else (-x*y*(1-x)*(x-y)*B[n-1]
                -x*(x*x+y-2*x*y)*Hx[n-1]+x*y*(1-x)*Hy[n-1]+x*(x-y)*A[n-1])
            need(den*B[n]==rhs,'SOURCE_FUNCTIONAL_SERIES',n)
    for x in [F(2,3),F(7,5)]:
        H=[sum(v*x**p for (p,s),v in h.items()) for h in hist[:N+1]]
        A=[sum(h.values()) for h in hist[:N+1]]
        for n in range(N+1):
            HF=0
            for m in range(n+1):
                k=n-m
                for (p,s),v in hist[m].items():
                    HF+=v*(int(k==0) if p==0 else comb(p+k-1,k)*x**k)
            rhs=(x-1)**2*H[n]+(1-x)*((x-1) if n==0 else -x**n)+(1-x)*A[n]
            if n:rhs+=-x**3*H[n-1]+x**2*A[n-1]
            need((1-x)*HF==rhs,'SCALAR_FUNCTIONAL_SERIES',n)

def orbit_coefficients(N):
    size=2*N+3;one=unit(size)
    # Reconstruct Lagrange root and check the cubic independently.
    X=[F(1)]+[binomial(F(3*n,2),n-1)/n for n in range(1,size)]
    w=add(X,scale(one,-1))
    need(add(mul(w,w),scale(shift(power(X,3),2),-1))==[0]*size,'FORMAL_KERNEL_ROOT')
    need(all(v>0 for v in X),'FORMAL_ROOT_POSITIVITY')
    previous=X;current=inv(add(one,scale(shift(X,2),-1)))
    q=add(X,scale(current,-1));r=inv(X)
    for j in range(N+2):
        following=inv(add(one,scale(shift(current,2),-1)))
        e=add(one,scale(div(current,previous),-1))
        c=add(one,scale(mul(current,e),-1))
        d=add(current,scale(following,-1))
        need(all(v==0 for v in e[:min(2*j+1,size)]),'FORMAL_E_VALUATION',j)
        need(all(v==0 for v in d[:min(2*j+3,size)]),'FORMAL_D_VALUATION',j)
        q=add(mul(c,q),d);r=add(mul(c,r),e)
        previous,current=current,following
    need(q[1]==1 and r[0]==1 and r[1]==-1,'FORMAL_QUOTIENT_LEADING')
    # X(-u) changes signs of odd coefficients; cancel the common 2u exactly.
    oddq=q[1:2*N+2:2];oddr=r[1:2*N+2:2]
    A=div(scale(oddq,-1),oddr)
    need(all(v.denominator==1 for v in A),'FORMAL_QUOTIENT_INTEGRAL')
    return [int(v) for v in A]

def enumeration(f):
    terms,hist=tree(f['ranges']['tree_n_max'])
    need(terms[:26]==f['sequences']['external_prefix'],'EXTERNAL_PREFIX')
    need(terms==f['sequences']['internal_terms'],'INTERNAL_TERMS')
    source_series(hist,16)
    need(brute(8)==terms[:9],'BRUTE_TREE_AGREEMENT')
    orbit=orbit_coefficients(f['ranges']['orbit_n_max'])
    need(orbit==terms[:len(orbit)],'ORBIT_TREE_AGREEMENT')
    need(all(terms[n+1]>terms[n] for n in range(1,len(terms)-1)),'FINITE_MONOTONICITY')
    targets=sorted({v+j for v in terms for j in [-1,0,1] if 0<v+j<=terms[-1]})
    for target in targets:
        n=next(j for j,v in enumerate(terms) if v>=target)
        need(terms[n]>=target and (n==0 or terms[n-1]<target),'FINITE_THRESHOLD_BOUNDARY')
    return {'tree_n_max':len(terms)-1,'orbit_n_max':len(orbit)-1,'brute_n_max':8,
            'source_and_scalar_series_n_max':16,'external_displayed_terms':26,
            'generated_terms_are_external':False,'finite_threshold_boundary_cases':len(targets),
            'terms_sha256':sha256(json.dumps(terms,separators=(',',':')).encode()).hexdigest()}

# Fixed-point integer interval arithmetic, independently implemented from the
# research certificate. Operations produce exact rational enclosing intervals.
SCALE=10**100
class I:
    def __init__(self,lo,hi=None,raw=False):
        if raw:self.lo,self.hi=lo,hi
        else:
            a=F(lo);b=F(lo if hi is None else hi)
            self.lo=(a.numerator*SCALE)//a.denominator
            self.hi=-((-b.numerator*SCALE)//b.denominator)
        need(self.lo<=self.hi,'INTERVAL_ORDER')
    def __add__(self,other):
        other=iv(other);return I(self.lo+other.lo,self.hi+other.hi,True)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo,True)
    def __sub__(self,other):return self+-iv(other)
    def __rsub__(self,other):return iv(other)+-self
    def __mul__(self,other):
        other=iv(other);p=[a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return I(min(p)//SCALE,-((-max(p))//SCALE),True)
    __rmul__=__mul__
    def reciprocal(self):
        need(not self.lo<=0<=self.hi,'INTERVAL_ZERO_DIVISOR')
        return I(SCALE*SCALE//self.hi,-((-SCALE*SCALE)//self.lo),True)
    def __truediv__(self,other):return self*iv(other).reciprocal()
    def __rtruediv__(self,other):return iv(other)*self.reciprocal()
    def sqrt(self):
        need(self.lo>=0,'INTERVAL_NEGATIVE_SQRT')
        return I(isqrt(self.lo*SCALE),isqrt(self.hi*SCALE)+1,True)
    def widen(self,error):return self+I(-error,error)
    def pair(self):return F(self.lo,SCALE),F(self.hi,SCALE)
    def __pow__(self,n):
        need(type(n) is int and n>=0,'INTERVAL_POWER')
        out=I(1)
        for _ in range(n):out=out*self
        return out
def iv(x):return x if isinstance(x,I) else I(x)

def decimal_outward(x,places,upper=False):
    x=F(x);S=10**places
    n=-((-x.numerator*S)//x.denominator) if upper else x.numerator*S//x.denominator
    sign='-' if n<0 else '';n=abs(n)
    return sign+str(n//S)+'.'+str(n%S).zfill(places)

def display(interval,places):
    lo,hi=interval.pair() if isinstance(interval,I) else interval
    return {'lower':decimal_outward(lo,places),'upper':decimal_outward(hi,places,True)}

def analytic_bound_arithmetic():
    # Joint holomorphy product-domain inequalities. The report supplies the proof.
    R=F(3,20);X=F(31,10);D=F(19,10)
    checks=[(1/(1-R*X)==F(200,107),'DOMAIN_INITIAL_IDENTITY'),
            (F(200,107)<D,'DOMAIN_INITIAL_BOUND'),
            (1/(1-R*D)==F(200,143)<D,'DOMAIN_INVARIANCE'),
            (R/(1-R*D)**2==F(6000,20449)<F(3,10),'DOMAIN_CONTRACTION'),
            (1+R*X==F(293,200),'DOMAIN_FIRST_RECIPROCAL'),
            (1+R*D==F(257,200),'DOMAIN_LATER_RECIPROCAL')]
    for condition,diagnostic in checks:need(condition,diagnostic)
    rho=F(4,27);h=F(1,1000);M=F(181,100);q=F(7,25);Pbound=2**230
    need(1/(1-rho*(3+h))<M,'TAIL_INITIAL_BOUND')
    need(1/(1-rho*M)<M,'TAIL_INVARIANCE')
    need(rho/(1-rho*M)**2<q,'TAIL_CONTRACTION')
    need(1/(1+rho*M)>F(3,4),'TAIL_ORBIT_LOWER')
    for a in [F(3),F(3,4)]:
        need(1/(abs(1-rho*a)+rho*h)>F(3,4),'TAIL_INITIAL_LOWER')
        need(rho*(a-h)/(1+rho*(a+h))>F(1,12),'TAIL_INITIAL_POLE_GAP')
    need(rho*F(3,4)/(1+rho*M)>F(1,12),'TAIL_LATER_POLE_GAP')
    # Locate the two fixed points by exact signs of their quadratic.
    # Fixed-point polynomial 1-x+rho*x^2: alpha in (1,5/4), beta in (5,28/5).
    need(1-1+rho>0 and 1-F(5,4)+rho*F(5,4)**2<0,'TAIL_ALPHA_RANGE')
    need(1-5+rho*25<0 and 1-F(28,5)+rho*F(28,5)**2>0,'TAIL_BETA_RANGE')
    need(M+F(5,4)<4,'TAIL_INITIAL_DISTANCE')
    need(rho*12*(M+F(28,5))<14,'TAIL_E_FACTOR')
    need(M*14<26,'TAIL_C_FACTOR')
    need(4*(1+q)<6,'TAIL_D_FACTOR')
    need(F(104)/(1-q)<145,'TAIL_PRODUCT_EXPONENT')
    need(3**145<Pbound,'TAIL_PRODUCT_POWER')
    need(3+h+M<5,'TAIL_Q_INITIAL')
    need(1/(F(3,4)-h)<2,'TAIL_R_INITIAL')
    need(5+F(6)/(1-q)<14,'TAIL_Q_BOUND')
    need(2+F(56)/(1-q)<80,'TAIL_R_BOUND')
    need((104*14*Pbound+6)/(1-q)<2**244,'TAIL_Q_SUM')
    need((104*80*Pbound+56)/(1-q)<2**244,'TAIL_R_SUM')
    E=F(2**244)*q**256
    need(E<F(1,10**67),'TAIL_NUMERICAL_SIZE')
    return E

def critical_orbit(center,steps,derivative=False):
    rho=I(F(4,27));previous=I(center);dp=I(1 if derivative else 0)
    current=1/(1-rho*previous);dc=rho*current*current*dp
    Q=previous-current;dQ=dp-dc;R=1/previous;dR=-dp/(previous*previous)
    for _ in range(steps):
        following=1/(1-rho*current);df=rho*following*following*dc
        # Canceled coefficient, unlike the original certificate's pole form.
        e=1-current/previous;de=-dc/previous+current*dp/(previous*previous)
        c=1-current*e;derc=-dc*e-current*de
        Q,dQ=c*Q+current-following,derc*Q+c*dQ+dc-df
        R,dR=c*R+e,derc*R+c*dR+de
        previous,current,dp,dc=current,following,dc,df
    return Q,R,dQ,dR

def atan_pair(k,n):
    value=sum((F((-1)**j,(2*j+1)*k**(2*j+1)) for j in range(n)),F(0))
    nextvalue=value+F((-1)**n,(2*n+1)*k**(2*n+1))
    return I(min(value,nextvalue),max(value,nextvalue))

def critical_values():
    E=analytic_bound_arithmetic()
    qp,rp,dqp,drp=critical_orbit(F(3),256,True)
    qm,rm,_,_=critical_orbit(F(3,4),256)
    qp,rp,qm,rm=[v.widen(E) for v in [qp,rp,qm,rm]]
    dqp,drp=[v.widen(1000*E) for v in [dqp,drp]]
    D=rp-rm;Num=qm-qp
    A=Num/D;derivative=(-dqp*D-Num*drp)/(D*D)
    need(D.hi<0,'CRITICAL_DETERMINANT_NEGATIVE')
    need(derivative.lo>0,'AMPLITUDE_DERIVATIVE_POSITIVE')
    a=F(1,5);twice=2*a/(1-a*a);four=2*twice/(1-twice*twice)
    need((four-F(1,239))/(1+four/F(239))==1,'MACHIN_TANGENT_IDENTITY')
    need(0<4*(F(1,5)-F(1,375))-F(1,239)<4*F(1,5)<F(3,2),'MACHIN_ANGLE_RANGE')
    pi=16*atan_pair(5,100)-4*atan_pair(239,30)
    sqrtfactor=(3/pi).sqrt();C=sqrtfactor*derivative
    a,b=sqrtfactor.pair();lo,hi=(3/pi).pair()
    need(0<a*a<=lo<=hi<b*b,'AMPLITUDE_SQRT_ENCLOSURE')
    values={'Q_plus':qp,'R_plus':rp,'Q_minus':qm,'R_minus':rm,
            'Q_plus_derivative':dqp,'R_plus_derivative':drp,'A_rho':A,
            'F_v':derivative,'pi':pi,'sqrt_3_over_pi':sqrtfactor,'C':C}
    for name,value in values.items():
        lo,hi=value.pair();need(hi-lo<F(1,10**60),'CRITICAL_INTERVAL_WIDTH',name)
    return values

def leading(f):
    values=critical_values()
    for name,value in values.items():
        need(display(value,55)==f['enclosures'][name],'ENCLOSURE_'+name.upper())
    return {'N':256,'arithmetic_decimal_scale':100,'printed_places':55,
            'tail':'2^244 (7/25)^256','derivative_tail_multiplier':1000,
            'C':display(values['C'],55),'F_v':display(values['F_v'],55),
            'finite_recurrence_uses_canceled_e':True}

def gamma_recurrence(alpha,K):
    # Derive transfer corrections from the exact gamma functional equation.
    # f(n+1)=(1+1/n)^alpha(1-alpha/n)f(n).
    size=K+3
    factor=add([binomial(alpha,j) for j in range(size)],
               scale(shift([binomial(alpha,j) for j in range(size)],1),-alpha))
    w=[0]+[(-1)**(j-1) for j in range(1,size)]
    powers=[power(w,j) for j in range(K+1)]
    result=[F(1)]+[F(0)]*K
    def residue():
        lhs=[0]*size
        for j,c in enumerate(result):lhs=add(lhs,scale(powers[j],c))
        return add(lhs,scale(mul(factor,result+[0]*(size-len(result))),-1))
    for j in range(1,K+1):
        constant=residue()[j+1];result[j]=1;slope=residue()[j+1]-constant
        need(slope!=0,'GAMMA_PIVOT');result[j]=-constant/slope
    need(residue()[:K+2]==[0]*(K+2),'GAMMA_FUNCTIONAL_RESIDUAL')
    return result

def bernoulli_numbers(N):
    # B1=-1/2 convention, directly from sum binom(n+1,k) Bk=0.
    B=[F(1)]
    for n in range(1,N+1):B.append(-sum(F(comb(n+1,k))*B[k] for k in range(n))/(n+1))
    return B

def gamma_bernoulli(alpha,K):
    B=bernoulli_numbers(K+1)
    def poly(n,x):return sum(F(comb(n,k))*B[k]*x**(n-k) for k in range(n+1))
    log=[0]+[(-1)**(m+1)*(poly(m+1,-alpha)-poly(m+1,F(1)))/(m*(m+1)) for m in range(1,K+1)]
    out=[F(1)]
    for n in range(1,K+1):out.append(sum(k*log[k]*out[n-k] for k in range(1,n+1))/n)
    return out

def gamma_checks(f):
    allvalues={}
    for j in range(4):
        alpha=F(2*j+1,2);v=gamma_recurrence(alpha,6)
        need(v==gamma_bernoulli(alpha,6),'GAMMA_BERNOULLI_AGREEMENT',str(alpha))
        allvalues[str(alpha)]=[str(x) for x in v]
    need(allvalues==f['gamma']['transfer_coefficients'],'GAMMA_TRANSFER_COEFFICIENTS')
    ratios=[F(1)]
    for j in range(1,4):ratios.append(ratios[-1]*(-F(2*j+1,2)))
    need([str(x) for x in ratios]==f['gamma']['gamma_ratios'],'GAMMA_RATIOS')
    need(allvalues['1/2'][1:3]==['3/8','25/128'],'GAMMA_FIRST_CORRECTIONS')
    need(ratios[1]*F(allvalues['3/2'][1])==F(-45,16),'RELATIVE_SECOND_CORRECTION')
    return {'half_integer_values':4,'order_each':6,'independent_methods':'functional equation and Bernoulli exponentiation',
            'relative_corrections':'d1=3/8-3b3/(2b1); d2=25/128-45b3/(16b1)+15b5/(4b1)'}
