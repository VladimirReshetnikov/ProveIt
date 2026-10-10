"""Two-variable Taylor jets through total degree three, over exact intervals."""
from __future__ import annotations
from math import factorial
from exact import I, as_i, log_integer, exp_nonnegative, neg_power

INDEX=((0,0),(1,0),(0,1),(2,0),(1,1),(0,2),(3,0),(2,1),(1,2),(0,3))
POS={ij:k for k,ij in enumerate(INDEX)}
PAIRS=[[(POS[(u,v)],POS[(i-u,j-v)]) for u in range(i+1) for v in range(j+1)] for i,j in INDEX]

class T:
    """Entries are divided derivatives: coefficient of da**i db**j."""
    __slots__=('c',)
    def __init__(self,c):
        self.c=tuple(c)
        if len(self.c)!=10:raise ValueError('ten coefficients required')
    @staticmethod
    def const(x):return T((as_i(x),)+(I.point(0),)*9)
    def __add__(self,o):
        o=as_t(o);return T(x+y for x,y in zip(self.c,o.c))
    __radd__=__add__
    def __neg__(self):return T(-x for x in self.c)
    def __sub__(self,o):return self+(-as_t(o))
    def __rsub__(self,o):return as_t(o)+(-self)
    def __mul__(self,o):
        o=as_t(o)
        return T(sum((self.c[j]*o.c[k] for j,k in ps),I.point(0)) for ps in PAIRS)
    __rmul__=__mul__
    def reciprocal(self):
        r=[self.c[0].reciprocal()]
        for n in range(1,10):
            r.append(-r[0]*sum((self.c[j]*r[k] for j,k in PAIRS[n] if j!=0),I.point(0)))
        return T(r)
    def __truediv__(self,o):return self*as_t(o).reciprocal()
    def __rtruediv__(self,o):return as_t(o)*self.reciprocal()
    def __pow__(self,n):
        if not isinstance(n,int) or n<0:raise ValueError('nonnegative integer required')
        r=T.const(1);v=self
        while n:
            if n&1:r=r*v
            n>>=1
            if n:v=v*v
        return r
    def derivative(self,i,j):return self.c[POS[(i,j)]]*factorial(i)*factorial(j)
    @property
    def v(self):return self.c[0]
    @property
    def a(self):return self.c[1]
    @property
    def b(self):return self.c[2]
    @property
    def aa(self):return 2*self.c[3]
    @property
    def ab(self):return self.c[4]
    @property
    def bb(self):return 2*self.c[5]

def as_t(x):return x if isinstance(x,T) else T.const(x)

def threshold_jets(A:I,B:I):
    r={};H=[I.point(0) for _ in range(4)];L2=log_integer(2)
    for n in range(2,8):
        j=n-1;L=log_integer(j);v=neg_power(j,B)
        for k in range(4):H[k]+=(-L)**k*v/factorial(k)
        L=log_integer(n)-L2 if n>2 else I.point(0)
        v=exp_nonnegative(A*L).reciprocal()
        r[n]=T((-L)**i*v*H[j]/factorial(i) for i,j in INDEX)
    s=r[3]
    K=(2*s*r[4]-s**3-r[5])/2
    # Q0 agrees identically with Q on K=0, including total b derivatives.
    Q0=-(r[4]*s**3-3*r[5]*s**2+3*r[6]*s-r[7])/2
    return K,Q0

def along_threshold(K:T,Q:T):
    ap=-K.b/K.a
    app=-(K.bb+2*K.ab*ap+K.aa*ap**2)/K.a
    def cubic(X):
        return (X.derivative(0,3)+3*X.derivative(1,2)*ap
                +3*X.derivative(2,1)*ap**2+X.derivative(3,0)*ap**3
                +3*(X.ab+X.aa*ap)*app)
    appp=-cubic(K)/K.a
    qp=Q.b+Q.a*ap
    qpp=Q.bb+2*Q.ab*ap+Q.aa*ap**2+Q.a*app
    qppp=cubic(Q)+Q.a*appp
    return qp,qpp,qppp
