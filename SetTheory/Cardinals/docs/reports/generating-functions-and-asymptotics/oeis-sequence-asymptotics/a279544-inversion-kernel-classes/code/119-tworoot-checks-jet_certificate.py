"""Independent N=400 degree-five interval-jet correction certificate.
Analytic disk/Cauchy arguments are proved in the report. This module verifies
all numerical bounds exactly and reconstructs the root jets from their cubic.
"""
from fractions import Fraction as F
from exact_math import I, SCALE, iv, add, mul, scale, unit, power, display, atan_pair
from support import need

class Q3:
    """Exact quadratic field a+b sqrt(3), for root reconstruction."""
    def __init__(self,a=0,b=0):self.a,self.b=F(a),F(b)
    def __add__(self,other):other=q3(other);return Q3(self.a+other.a,self.b+other.b)
    __radd__=__add__
    def __neg__(self):return Q3(-self.a,-self.b)
    def __sub__(self,other):return self+-q3(other)
    def __rsub__(self,other):return q3(other)+-self
    def __mul__(self,other):
        other=q3(other);return Q3(self.a*other.a+3*self.b*other.b,self.a*other.b+self.b*other.a)
    __rmul__=__mul__
    def __truediv__(self,other):
        other=q3(other);norm=other.a*other.a-3*other.b*other.b
        need(norm!=0,'ROOT_FIELD_ZERO_DIVISOR')
        return self*Q3(other.a/norm,-other.b/norm)
    def __rtruediv__(self,other):return q3(other)/self
    def __eq__(self,other):other=q3(other);return self.a==other.a and self.b==other.b
    def __bool__(self):return bool(self.a or self.b)
    def interval(self):return I(self.a)+I(self.b)*I(3).sqrt()
    def pair(self):return [str(self.a),str(self.b)]
def q3(x):return x if isinstance(x,Q3) else Q3(x)

def roots():
    n=7;one=unit(n,Q3(1));z=[Q3(F(4,27)),0,Q3(F(-4,27))]+[0]*(n-3)
    def residue(x):return add(power(add(x,scale(one,-1)),2),scale(mul(z,power(x,3)),-1))
    plus=[Q3(3),Q3(0,-2)]+[Q3(0)]*(n-2)
    minus=[Q3(F(3,4))]+[Q3(0)]*(n-1)
    for k in range(2,6):
        const=residue(plus)[k+1];plus[k]=Q3(1);pivot=residue(plus)[k+1]-const
        need(bool(pivot),'ROOT_PLUS_PIVOT');plus[k]=-const/pivot
    need(all(v==0 for v in residue(plus)),'ROOT_PLUS_RESIDUAL')
    for k in range(1,6):
        const=residue(minus)[k];minus[k]=Q3(1);pivot=residue(minus)[k]-const
        need(bool(pivot),'ROOT_MINUS_PIVOT');minus[k]=-const/pivot
    need(all(v==0 for v in residue(minus)[:6]),'ROOT_MINUS_RESIDUAL')
    need(all(minus[k]==0 for k in [1,3,5]),'ROOT_MINUS_EVEN')
    need(plus[1]==Q3(0,-2),'ROOT_PLUS_BRANCH')
    return plus[:6],minus[:6]

class Box:
    """Rectangular complex intervals, with a sharper exact real-square bound."""
    def __init__(self,re=0,im=0):self.re,self.im=iv(re),iv(im)
    def __add__(self,other):other=box(other);return Box(self.re+other.re,self.im+other.im)
    __radd__=__add__
    def __neg__(self):return Box(-self.re,-self.im)
    def __sub__(self,other):return self+-box(other)
    def __rsub__(self,other):return box(other)+-self
    def __mul__(self,other):
        other=box(other);return Box(self.re*other.re-self.im*other.im,self.re*other.im+self.im*other.re)
    __rmul__=__mul__
    def reciprocal(self):
        def square(v):
            a,b=v.pair();return I(0 if a<=0<=b else min(a*a,b*b),max(a*a,b*b))
        norm=square(self.re)+square(self.im)
        need(norm.lo>0,'COMPLEX_BOX_ZERO_DIVISOR')
        return Box(self.re/norm,-self.im/norm)
    def __truediv__(self,other):return self*box(other).reciprocal()
    def __rtruediv__(self,other):return box(other)*self.reciprocal()
    def norm1(self):return F(max(abs(self.re.lo),abs(self.re.hi))+max(abs(self.im.lo),abs(self.im.hi)),SCALE)
def box(x):return x if isinstance(x,Box) else Box(x)
def rectangle(center,r):return Box(I(center-r,center+r),I(-r,r))

class Jet:
    degree=5
    def __init__(self,a=0):
        a=a if type(a) is list else [a]
        need(len(a)<=self.degree+1,'JET_LENGTH')
        self.a=[iv(v) for v in a]+[I(0)]*(self.degree+1-len(a))
    def __add__(self,other):other=jet(other);return Jet(add(self.a,other.a))
    __radd__=__add__
    def __neg__(self):return Jet(scale(self.a,-1))
    def __sub__(self,other):return self+-jet(other)
    def __rsub__(self,other):return jet(other)+-self
    def __mul__(self,other):return Jet(mul(self.a,jet(other).a))
    __rmul__=__mul__
    def reciprocal(self):
        out=[1/self.a[0]]
        for n in range(1,self.degree+1):
            out.append(-sum((self.a[k]*out[n-k] for k in range(1,n+1)),I(0))/self.a[0])
        return Jet(out)
    def __truediv__(self,other):return self*jet(other).reciprocal()
    def __rtruediv__(self,other):return jet(other)*self.reciprocal()
def jet(x):return x if isinstance(x,Jet) else Jet(x)

def bounds():
    h=F(1,100000);rho=F(4,27);R=F(149,1000);M=F(181,100);q=F(7,25)
    low=rho*(1-h*h);high=rho*(1+h*h);seed=F(1,1000)
    # Root disk estimates: rational checks of every displayed bound. The
    # elementary analytic sine/cosine estimates are justified in the report.
    need(F(1)/(1-h*h)<F(9,4),'JET_ASIN_BOUND')
    need(F(1)/(1-h)<2,'JET_COSH_MAJORANT')
    need(18*h/(1-6*h)<20*h<seed,'JET_PLUS_SEED_DISK')
    need(F(3,8)*h*h/(1-h*h/2)<h*h<seed,'JET_MINUS_SEED_DISK')
    need(high<R,'JET_Z_BOUND')
    need(1/(1-R*(3+seed))<M,'JET_INITIAL_BOUND')
    need(1/(1-R*M)<M,'JET_INVARIANCE')
    need(R/(1-R*M)**2<q,'JET_CONTRACTION')
    need(1/(1+R*M)>F(3,4),'JET_ORBIT_LOWER')
    for c in [F(3),F(3,4)]:
        need(1/(abs(1-rho*c)+rho*h*h*c+R*seed)>F(3,4),'JET_INITIAL_LOWER')
        need(low*(c-seed)/(1+R*(c+seed))>F(1,12),'JET_INITIAL_POLE_GAP')
    need(low*F(3,4)/(1+R*M)>F(1,12),'JET_LATER_POLE_GAP')
    need(R*F(25,16)<F(1,4),'JET_ALPHA_BOUND')
    need(1/low+F(5,4)<9,'JET_BETA_BOUND')
    need(M+F(5,4)<4,'JET_INITIAL_DISTANCE')
    need(R*12*(M+9)<20,'JET_E_FACTOR')
    need(M*20<37,'JET_C_FACTOR')
    need(4*(1+q)<6,'JET_D_FACTOR')
    need(F(148)/(1-q)<206,'JET_PRODUCT_EXPONENT')
    Pbound=2**327
    need(3**206<Pbound,'JET_PRODUCT_POWER')
    need(3+seed+M<5,'JET_Q_INITIAL')
    need(1/(F(3,4)-seed)<2,'JET_R_INITIAL')
    need(5+F(6)/(1-q)<14,'JET_Q_BOUND')
    need(2+F(80)/(1-q)<114,'JET_R_BOUND')
    need((148*14*Pbound+6)/(1-q)<2**342,'JET_Q_TAIL')
    need((148*114*Pbound+80)/(1-q)<2**342,'JET_R_TAIL')
    E=F(2**342)*q**400
    need(2*E<F(1,2),'JET_DENOMINATOR_TAIL')
    # |F-F_N| <= (2E+|F_N|2E)/(|D_N|-2E) <12E<16E.
    need((2+2*2)/F(1,2)==12<16,'JET_QUOTIENT_TAIL_FACTOR')
    return E,h

def orbit(z,X,N):
    predecessor=X;current=1/(1-z*X);Q=X-current;R=1/X
    for _ in range(N):
        following=1/(1-z*current)
        e=1-current/predecessor;c=1-current*e
        Q,R=c*Q+current-following,c*R+e
        predecessor,current=current,following
    return Q,R

def compute():
    E,h=bounds();rho=F(4,27)
    qp,rp=orbit(rectangle(rho,rho*h*h),rectangle(F(3),20*h),400)
    qm,rm=orbit(rectangle(rho,rho*h*h),rectangle(F(3,4),h*h),400)
    den=rp-rm;num=qm-qp
    need(-2*SCALE<den.re.lo<=den.re.hi<-SCALE,'JET_RECTANGLE_DENOMINATOR')
    need(num.norm1()<2,'JET_RECTANGLE_NUMERATOR')
    xp,xm=roots();z=Jet([rho,0,-rho])
    qp,rp=orbit(z,Jet([v.interval() for v in xp]),400)
    qm,rm=orbit(z,Jet([v.interval() for v in xm]),400)
    result=(qm-qp)/(rp-rm)
    b={j:result.a[j].widen(16*E/h**j) for j in [1,3,5]}
    pi=16*atan_pair(5,100)-4*atan_pair(239,30)
    C=-b[1]/(2*pi.sqrt())
    c1=F(3,8)-F(3,2)*b[3]/b[1]
    c2=F(25,128)-F(45,16)*b[3]/b[1]+F(15,4)*b[5]/b[1]
    need(b[1].hi<0 and C.lo>0,'JET_AMPLITUDE_POSITIVITY')
    values={'C':C,'c1':c1,'c2':c2,**{'b'+str(j):b[j] for j in b}}
    for name,v in values.items():
        lo,hi=v.pair();need(hi-lo<F(1,10**77),'JET_ENCLOSURE_WIDTH',name)
    return values,{'D_real':den.re,'D_imag':den.im,'N_norm1_upper':num.norm1()},xp,xm

def check(f):
    values,den,xp,xm=compute();fixture=f['corrections']
    for key,root in [('plus',xp),('minus',xm)]:
        need([v.pair() for v in root]==fixture['root_jets'][key],'JET_ROOT_'+key.upper())
    for name,v in values.items():
        need(display(v,80)==fixture['enclosures'][name],'JET_ENCLOSURE_'+name.upper())
    for name in ['D_real','D_imag']:
        need(display(den[name],12)==fixture['rectangle'][name],'JET_RECTANGLE_'+name.upper()+'_FIXTURE')
    need(str(den['N_norm1_upper'])==fixture['rectangle']['N_norm1_upper'],'JET_RECTANGLE_N_NORM1_FIXTURE')
    return {'N':400,'degree':5,'disk_radius':'1/100000','tail':'2^342 (7/25)^400',
            'coefficient_error':'16 E 10^(5j), j=1,3,5',
            'C':display(values['C'],80),'c1':display(values['c1'],80),'c2':display(values['c2'],80),
            'root_jets':'reconstructed in Q(sqrt(3)) from the cubic',
            'rectangle_denominator_real':display(den['D_real'],12),
            'rectangle_numerator_norm1_less_than':2}
