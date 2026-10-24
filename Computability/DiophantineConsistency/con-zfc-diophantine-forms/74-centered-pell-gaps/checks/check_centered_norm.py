"""Independent exact identities, not a consistency-equivalence checker."""
import json
from pathlib import Path
from collections import defaultdict

class Poly:
    N=5
    def __init__(self, terms):
        self.terms={k:v for k,v in terms.items() if v}
    @classmethod
    def const(cls,v):
        return cls({(0,)*cls.N:v})
    @classmethod
    def var(cls,i):
        e=[0]*cls.N
        e[i]=1
        return cls({tuple(e):1})
    def __add__(self, other):
        if not isinstance(other,Poly): other=Poly.const(other)
        d=defaultdict(int,self.terms)
        for e,c in other.terms.items(): d[e]+=c
        return Poly(d)
    __radd__=__add__
    def __neg__(self): return Poly({e:-c for e,c in self.terms.items()})
    def __sub__(self,other): return self+-other
    def __rsub__(self,other): return -self+other
    def __mul__(self,other):
        if not isinstance(other,Poly): other=Poly.const(other)
        d=defaultdict(int)
        for e,c in self.terms.items():
            for f,b in other.terms.items():
                d[tuple(a+z for a,z in zip(e,f))]+=c*b
        return Poly(d)
    __rmul__=__mul__
    def is_zero(self): return not self.terms

n,f0,e,V,Q=[Poly.var(i) for i in range(5)]
D=f0*f0+e
x=n+f0+V
B=2*(Q-1)*x
H=(Q-1)*(n*n+2*V*n+e)-V*V+1
A=(Q-1)*(x*x+D)-Q*V*V+1
checks={
    'centered_numerator':(A-H-B*f0).is_zero(),
    'centered_norm':(A*A-B*B*D-(H*H+2*B*f0*H-B*B*e)).is_zero(),
}
d,delta,Z,c,t=[Poly.var(i) for i in range(5)]
v=d*Z-c
q=delta*(d-1)
a=(q-1)*(t*t+d)-q*v*v+1
g=1+delta*c*c
quo=(delta*t*t+delta*d-delta-1
     -delta*d*d*Z*Z+delta*d*Z*Z
     +2*delta*d*Z*c-2*delta*Z*c-delta*c*c)
checks['modulus_identity']=(a-g+(delta+1)*t*t-d*quo).is_zero()
if not all(checks.values()):
    raise SystemExit('Exact identity failure: '+repr(checks))
result={'checks':checks,'scope':'exact symbolic identities only',
        'method':'independent sparse multivariate integer polynomials; standard library only'}
out=Path(__file__).with_name('CENTERED_NORM_CHECK.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
