"""Independent eigenvalue-coordinate integration of the two corrections.

Unlike the producer's matrix-entry Wick expansion, this integrates the
Vandermonde-square density directly in m-1 trace-zero coordinates.
"""
from functools import lru_cache
from pathlib import Path
import json
import sympy as s

records=[]
for m in (2,3,4):
    x=s.symbols('x:'+str(m-1)); y=(*x,-sum(x))
    delta=s.prod(y[i]-y[j] for i in range(m) for j in range(i+1,m))**2
    cov=[[s.Rational((m if i==j else 0)-1,4*m) for j in range(m-1)] for i in range(m-1)]
    @lru_cache(None)
    def gauss(e):
        if sum(e)%2:return s.S.Zero
        if not any(e):return s.S.One
        i=next(i for i,n in enumerate(e) if n)
        f=list(e);f[i]-=1;out=0
        for j,n in enumerate(f):
            if n:
                g=f.copy();g[j]-=1
                out+=n*cov[i][j]*gauss(tuple(g))
        return out
    def integral(poly):
        return sum(c*gauss(e) for e,c in s.Poly(poly,*x).terms())
    base=integral(delta)
    def moment(powers):
        return s.factor(integral(delta*s.prod(sum(v**p for v in y) for p in powers))/base)
    needed=((2,),(4,),(6,),(2,2),(2,4),(4,4))
    v={p:moment(p) for p in needed}
    a=-s.Rational(m*m-1,3*m)
    c1=s.factor(a+m*v[(2,)]-s.Rational(4,3)*v[(4,)])
    L2=-s.Rational(4,3)*v[(2,)]+s.Rational(m,2)*v[(4,)]-s.Rational(32,15)*v[(6,)]+s.Rational(3,2)*v[(2,2)]
    L11=a*a+m*m*v[(2,2)]+s.Rational(16,9)*v[(4,4)]+2*a*m*v[(2,)]-s.Rational(8,3)*a*v[(4,)]-s.Rational(8,3)*m*v[(2,4)]
    c2=s.factor(L2+L11/2)
    want1=s.Rational((m*m-1)**2,12*m)
    want2=s.Rational((m*m-1)*(m**6+3*m*m-1),288*m*m)
    if (c1,c2)!=(want1,want2):raise RuntimeError((m,c1,c2,want1,want2))
    records.append({'m':m,'Vandermonde_integral':str(base),'moments':{str(p):str(v[p]) for p in needed},'c1':str(c1),'c2':str(c2)})

# Independent formal reversion, with logarithm treated as a symbol.
z,A,d1,d2,H=s.symbols('z A d1 d2 H')
w_over_y=1+A*H*z+(A*A*H-d1)*z*z+(-A**3*H**2/2+(A**3+A*d1)*H-A*d1-d2)*z**3
res=s.series((w_over_y-1)/z-A*(H+s.log(w_over_y))+d1*z/w_over_y+d2*z*z/w_over_y**2,z,0,3).removeO().expand()
if s.simplify(res)!=0:raise RuntimeError(('inverse',res))
out={'passed':True,'method':'Direct trace-zero Gaussian eigenvalue integrals with Vandermonde-square weight','records':records,'inverse_reversion_passed':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
