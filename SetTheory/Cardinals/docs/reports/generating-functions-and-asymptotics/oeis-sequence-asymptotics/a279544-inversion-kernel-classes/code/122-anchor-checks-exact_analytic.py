"""Active exact certificate implementation for report122.
The lattice/dual/rectangle/jet formulas and analytic estimates are reimplemented
from the audited producer certificates, not an independent formal proof of
holomorphy or singularity transfer. All endpoints and bounds are rational.
"""
from fractions import Fraction as F
from math import isqrt
from exact_model import require

SCALE=10**120

def canonical(x):
    x=F(x)
    return str(x.numerator)+'/'+str(x.denominator)


def ceiling(a,b): return -((-a)//b)


class Interval:
    def __init__(self, lower=0, upper=None, lattice=False):
        if lattice:
            self.lo,self.hi=lower,upper
        else:
            a,b=F(lower),F(lower if upper is None else upper)
            self.lo=a.numerator*SCALE//a.denominator
            self.hi=ceiling(b.numerator*SCALE,b.denominator)
        require(self.lo<=self.hi,'interval: reversed endpoints')
    def coerce(self,x): return x if isinstance(x,Interval) else Interval(x)
    def __add__(self,x):
        x=self.coerce(x)
        return Interval(self.lo+x.lo,self.hi+x.hi,lattice=True)
    __radd__=__add__
    def __neg__(self): return Interval(-self.hi,-self.lo,lattice=True)
    def __sub__(self,x): return self+-self.coerce(x)
    def __rsub__(self,x): return self.coerce(x)+-self
    def __mul__(self,x):
        x=self.coerce(x)
        values=(self.lo*x.lo,self.lo*x.hi,self.hi*x.lo,self.hi*x.hi)
        return Interval(min(values)//SCALE,ceiling(max(values),SCALE),lattice=True)
    __rmul__=__mul__
    def inv(self):
        require(not self.lo<=0<=self.hi,'interval: denominator contains zero')
        return Interval(SCALE*SCALE//self.hi,ceiling(SCALE*SCALE,self.lo),lattice=True)
    def __truediv__(self,x): return self*self.coerce(x).inv()
    def __rtruediv__(self,x): return self.coerce(x)*self.inv()
    def sqrt(self):
        require(self.lo>=0,'interval: negative square-root domain')
        a,b=isqrt(self.lo*SCALE),isqrt(self.hi*SCALE)
        return Interval(a,b+(b*b!=self.hi*SCALE),lattice=True)
    def expand(self,r): return self+Interval(-r,r)
    def strictly_inside(self,lo,hi): return F(self.lo,SCALE)>F(lo) and F(self.hi,SCALE)<F(hi)
    def endpoints(self): return [canonical(F(self.lo,SCALE)),canonical(F(self.hi,SCALE))]
    def maxabs(self): return F(max(abs(self.lo),abs(self.hi)),SCALE)


class Jet:
    def __init__(self,values=0,degree=5):
        self.degree=degree
        if not isinstance(values,list): values=[values]
        require(len(values)<=degree+1,'jet: excessive degree')
        self.a=[v if isinstance(v,Interval) else Interval(v) for v in values]+[Interval()]*(degree+1-len(values))
    def coerce(self,x): return x if isinstance(x,Jet) else Jet(x,self.degree)
    def __add__(self,x):
        x=self.coerce(x)
        return Jet([u+v for u,v in zip(self.a,x.a)],self.degree)
    __radd__=__add__
    def __neg__(self): return Jet([-v for v in self.a],self.degree)
    def __sub__(self,x): return self+-self.coerce(x)
    def __rsub__(self,x): return self.coerce(x)+-self
    def __mul__(self,x):
        x=self.coerce(x)
        return Jet([sum((self.a[i]*x.a[n-i] for i in range(n+1)),Interval()) for n in range(self.degree+1)],self.degree)
    __rmul__=__mul__
    def inv(self):
        inv0=self.a[0].inv(); out=[inv0]
        for n in range(1,self.degree+1):
            out.append(-sum((self.a[k]*out[n-k] for k in range(1,n+1)),Interval())*inv0)
        return Jet(out,self.degree)
    def __truediv__(self,x): return self*self.coerce(x).inv()
    def __rtruediv__(self,x): return self.coerce(x)*self.inv()


class Rectangle:
    def __init__(self,real=0,imag=0):
        self.real=real if isinstance(real,Interval) else Interval(real)
        self.imag=imag if isinstance(imag,Interval) else Interval(imag)
    def coerce(self,x): return x if isinstance(x,Rectangle) else Rectangle(x)
    def __add__(self,x):
        x=self.coerce(x)
        return Rectangle(self.real+x.real,self.imag+x.imag)
    __radd__=__add__
    def __neg__(self): return Rectangle(-self.real,-self.imag)
    def __sub__(self,x): return self+-self.coerce(x)
    def __rsub__(self,x): return self.coerce(x)+-self
    def __mul__(self,x):
        x=self.coerce(x)
        return Rectangle(self.real*x.real-self.imag*x.imag,self.real*x.imag+self.imag*x.real)
    __rmul__=__mul__
    def inv(self):
        denominator=self.real*self.real+self.imag*self.imag
        return Rectangle(self.real/denominator,-self.imag/denominator)
    def __truediv__(self,x): return self*self.coerce(x).inv()
    def __rtruediv__(self,x): return self.coerce(x)*self.inv()
    def bound(self): return self.real.maxabs()+self.imag.maxabs()


def phi(z,x): return 1+z*x/((1-z*x)*(1-z*x))


def finite_orbit(z,x,v,iterations,p=None):
    for _ in range(iterations):
        nx=phi(z,x); d=(x-nx)/(z*x); c=1-(1-z*x)*d
        v=c*v+d
        if p is not None: p=c*p
        x=nx
    return (v,p) if p is not None else v


def pi_enclosure():
    def atan(q,n):
        partial=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0))
        endpoint=partial+F((-1)**n,(2*n+1)*q**(2*n+1))
        return Interval(min(partial,endpoint),max(partial,endpoint))
    return 16*atan(5,120)-4*atan(239,40)


def root_jet_check(coefficients):
    # Q(sqrt(3)) pairs; an independent exact residual through t^6 determines
    # the printed degree-five branch, with its negative linear coefficient.
    coeff=[tuple(F(x) for x in row) for row in coefficients]+[(F(0),F(0))]
    def add(a,b): return (a[0]+b[0],a[1]+b[1])
    def mul(a,b): return (a[0]*b[0]+3*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    def conv(a,b): return [sum_pair([mul(a[j],b[n-j]) for j in range(n+1)]) for n in range(7)]
    def sum_pair(items):
        ans=(F(0),F(0))
        for item in items: ans=add(ans,item)
        return ans
    cube=conv(conv(coeff,coeff),coeff)
    for n in range(7):
        rhs=tuple(F(4,27)*(cube[n][k]-(cube[n-2][k] if n>=2 else 0)) for k in range(2))
        res=tuple(coeff[n][k]-(int(n==0 and k==0))-rhs[k] for k in range(2))
        require(res==(0,0),'root: Puiseux equation residual through t^6')
    require(coeff[0]==(F(3,2),0) and coeff[1]==(0,F(-1,2)),'root: wrong critical branch')


def rational_premises(data):
    p={k:F(v) for k,v in data['parameters'].items()}
    rho,h,r,Z,M,q=p['rho'],p['h'],p['r'],p['Z'],p['M'],p['q']
    N=data['iterations']; E=F(data['tail_E'])
    require(rho==F(4,27),'domain: wrong critical rho')
    require(0<h<F(1,60) and 0<r and 0<q<1,'domain: invalid positive radii or contraction')
    require(q==F(1,2),'tail: this geometric constant requires q=1/2')
    # Large joint holomorphy domain from the proof.
    zlarge,Rlarge,xlarge=F(3,20),F(151,100),F(181,100)
    require(Rlarge**2<F(23,10),'joint-domain: squared root radius')
    require(F(69,200)/F(131,200)**2<F(81,100),'joint-domain: upper seed radius')
    require(zlarge*(1+zlarge*xlarge)/(1-zlarge*xlarge)**3<F(1,2),'joint-domain: contraction')
    require(zlarge*xlarge/(1-zlarge*xlarge)**2<F(52,100),'joint-domain: invariant image')
    zlo,zhi=rho*(1-h*h),rho*(1+h*h)
    require(zhi<Z and 1/zlo<7,'domain: complex z disk exceeds bound')
    require(Z*M<1,'domain: orbit map pole enters majorant disk')
    require(Z*(1+Z*M)/(1-Z*M)**3<q,'domain: complex contraction bound fails')
    xmax=(F(3,2)+r)**2
    require(xmax<F(226,100),'domain: seed argument bound')
    require(Z*(1+Z*xmax)/(1-Z*xmax)**3<F(11,10),'domain: seed x derivative bound')
    require(xmax*(1+Z*xmax)/(1-Z*xmax)**3<11,'domain: seed z derivative bound')
    require(M*(1+Z*M)/(1-Z*M)**3<6,'domain: orbit z derivative bound')
    require(F(11,10)*(3+r)*r+11*rho*h*h<F(1,250),'domain: seed perturbation bound')
    require(F(1,250)+12*rho*h*h<F(1,200),'domain: propagated perturbation bound')
    require(F(7,4)+F(1,200)<M and 1-F(1,200)>F(99,100),'domain: orbit modulus bounds')
    require(F(7,4)-F(589,400)<F(28,100),'tail: upper reference initial difference')
    require(rho/(1-rho)**2<F(21,100),'tail: lower reference initial difference')
    require(F(28,100)+F(3,2)*F(1,250)+6*rho*h*h<F(3,10),'tail: complex initial difference')
    require(7*F(3,10)/F(99,100)<F(11,5),'tail: d increment bound')
    require((1+Z*M)*F(11,5)<3,'tail: c increment bound')
    require(3**6<2**10 and 2+F(22,5)<7,'tail: finite product and affine bound')
    require(2*(3*7*2**10+F(11,5))<2**16,'tail: common remainder majorant')
    require(E>=2**16*q**N,'tail: claimed E is smaller than proved remainder')
    require(E<F(1,2),'tail: quotient denominator error too large')
    require(F(101,100)**3/F(299,100)<F(3,5)**2,'cauchy: Lagrange reciprocal-root bound')
    require(F(9,10)/(1-60*h)<1,'cauchy: critical root leaves t disk enclosure')
    require(h<=r,'cauchy: t image outside R disk')
    require(F(data['derivative_tail'])>=E/r,'tail: derivative Cauchy remainder too small')
    for j in (1,3,5):
        require(F(data['coefficient_tails'][str(j)])>=2*E/h**j,'tail: coefficient Cauchy remainder too small')
    # Independent rational replay of the strengthened global denominator lemma.
    B=F(data['denominator_disk_B']); w=Z*B
    require(rho<Z<F(3,20) and 1<B<2 and w<1,'global: invalid zero-free domain')
    increment=w/(1-w)**2
    require(increment<B-1,'global: lower-orbit disk is not invariant')
    L=Z*(1+w)/(1-w)**3; K=(1+w)/((1-Z)**2*(2-B))
    require(0<L<F(7,20) and 0<K<F(5,2),'global: contraction or prefactor bound')
    require(K*L<F(7,8),'global: individual denominator factor may vanish')
    require(K*L/(1-L)<F(4,3),'global: product logarithm bound')
    require(8*F(4,3)==F(32,3)<11,'global: exponent bound')
    c0=(2-Z)/(1+Z); lower=c0/F(3**11)
    require(c0>1 and lower>F(data['denominator_modulus_floor']),'global: claimed denominator floor too large')
    root_jet_check(data['root_jet'])
    return {'rho':canonical(rho),'tail_E':canonical(E),'derivative_tail':data['derivative_tail'],
            'coefficient_tails':data['coefficient_tails'],'global_Z':canonical(Z),'global_B':canonical(B),
            'global_L':canonical(L),'global_K':canonical(K),'global_KL':canonical(K*L),
            'global_KL_over_1_minus_L':canonical(K*L/(1-L)),'global_c0_floor':canonical(c0),
            'global_P_floor':canonical(lower),'root_equation_verified_through_t':6}


def analytic_checks(data,preflight=False):
    bounds=rational_premises(data)
    if preflight: return bounds
    rho,h,r=(F(data['parameters'][k]) for k in ('rho','h','r'))
    N=data['iterations']; E=F(data['tail_E']); pi=pi_enclosure(); sqrt3=Interval(3).sqrt()
    z=Jet(rho,1); R=Jet([F(3,2),1],1)
    V=finite_orbit(z,phi(z,R*R),R,N)
    Q,P=finite_orbit(z,Jet(1,1),Jet(0,1),N,Jet(1,1))
    V.a[0]=V.a[0].expand(E); V.a[1]=V.a[1].expand(F(data['derivative_tail']))
    Q.a[0]=Q.a[0].expand(E); P.a[0]=P.a[0].expand(E)
    G=(V-Q)/P; amplitude=sqrt3*G.a[1]/(4*pi.sqrt())
    for name,value in [('F',G.a[0]),('G_R',G.a[1]),('C',amplitude)]:
        require(value.strictly_inside(*data['claimed_intervals'][name]),'interval: '+name+' outside claimed interval')
    def box(center,radius): return Rectangle(Interval(center-radius,center+radius),Interval(-radius,radius))
    z=box(rho,rho*h*h); R=box(F(3,2),h)
    v=finite_orbit(z,phi(z,R*R),R,N)
    q,p=finite_orbit(z,Rectangle(1),Rectangle(0),N,Rectangle(1))
    require(p.real.strictly_inside(3,4),'quotient: complex denominator real part not in (3,4)')
    complex_p_real=p.real.endpoints()
    numerator_bound=(v-q).bound()
    require(numerator_bound<5,'quotient: complex numerator bound is not below 5')
    # |G-G_N| <= 2E/(3-E) + 5E/[3(3-E)] < 2E.
    require(2/(3-E)+F(5,3)/(3-E)<2,'quotient: 2E error estimate fails')
    root=[Interval(F(a))+F(b)*sqrt3 for a,b in data['root_jet']]
    z=Jet([rho,0,-rho]); R=Jet(root)
    v=finite_orbit(z,phi(z,R*R),R,N)
    q,p=finite_orbit(z,Jet(1),Jet(0),N,Jet(1)); finite=(v-q)/p
    b={j:finite.a[j].expand(F(data['coefficient_tails'][str(j)])) for j in (1,3,5)}
    C=-b[1]/(2*pi.sqrt())
    d1=F(3,8)-F(3,2)*b[3]/b[1]
    d2=F(25,128)-F(45,16)*b[3]/b[1]+F(15,4)*b[5]/b[1]
    for name,value in [('C',C),('d1',d1),('d2',d2)]:
        require(value.strictly_inside(*data['claimed_intervals'][name]),'interval: '+name+' outside claimed interval')
    require(max(amplitude.lo,C.lo)<=min(amplitude.hi,C.hi),'interval: two C enclosures disjoint')
    return {**bounds,'iterations':N,'lattice_decimal_digits':120,'F':G.a[0].endpoints(),
            'G_R':G.a[1].endpoints(),'C_derivative':amplitude.endpoints(),'C_Puiseux':C.endpoints(),
            'P':P.a[0].endpoints(),'b1':b[1].endpoints(),'b3':b[3].endpoints(),'b5':b[5].endpoints(),
            'd1':d1.endpoints(),'d2':d2.endpoints(),'complex_P_real':complex_p_real,
            'complex_numerator_norm1_bound':canonical(numerator_bound),'pi':pi.endpoints()}
