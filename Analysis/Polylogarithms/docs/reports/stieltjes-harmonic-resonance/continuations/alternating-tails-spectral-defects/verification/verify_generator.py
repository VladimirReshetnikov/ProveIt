"""Independent high precision checks for the cyclotomic parity generator."""
from __future__ import annotations
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 65

def F(z,t):
    """Color z is represented exactly by (integer residue, conductor)."""
    r,N=z
    if r % N == 0:
        return -mp.digamma(1-t)-mp.euler
    return -sum(mp.exp(2j*mp.pi*r*k/N)*mp.digamma((k-t)/N)
                for k in range(1,N+1))/N

def B(z,t):
    r,N=z; theta=mp.mpf(r%N)/N
    if not t: return mp.mpf(1)
    if not r%N: return mp.pi*t*mp.cot(mp.pi*t)
    return mp.pi*t*mp.exp(1j*mp.pi*(2*theta-1)*t)/mp.sin(mp.pi*t)

def inv(z): return ((-z[0])%z[1],z[1])
def mul(a,b):
    assert a[1]==b[1]
    return ((a[0]+b[0])%a[1],a[1])
def neg(a):
    assert not a[1]%2
    return ((a[0]+a[1]//2)%a[1],a[1])

def dd(f,x,y):
    return mp.diff(f,x) if x==y else (f(x)-f(y))/(x-y)

def G(a,b,X,Y):
    c=mul(a,b)
    p=(B(c,X)*F(b,Y-X)-B(a,X)*F(b,Y))/X
    q=-(B(c,Y)*F(inv(a),Y-X)-F(inv(a),-X))/Y
    return p+q-dd(lambda t:F(c,t),X,Y)

def P(a,b,x,y):
    return (G(a,b,x,y)+G(a,b,x,-y)
            -G(a,b,-x,y)-G(a,b,-x,-y))/(4*x)

def H(c,x,y):
    def O(t):return (F(c,t)+F(c,-t))/2
    return mp.diff(O,x)/(2*x) if x==y else (O(x)-O(y))/(x*x-y*y)

def master(a,b,x,y):
    c=neg(mul(a,b))
    return -P(a,neg(b),x,y)-P(b,neg(a),y,x)-H(c,x,y)-H(inv(c),x,y)

def tail(a,x,n):
    r,N=a
    if not x:
        return sum(mp.exp(2j*mp.pi*r*(n+k)/N)*mp.polygamma(1,(n+k)/N)
                   for k in range(1,N+1))/(N*N)
    return sum(mp.exp(2j*mp.pi*r*(n+k)/N)*
               (mp.digamma((n+k+x)/N)-mp.digamma((n+k-x)/N))
               for k in range(1,N+1))/(2*N*x)

def direct(a,b,x,y):
    def term(n):
        return (-1)**n*(2*n+1)*tail(a,x,n)*tail(b,y,n)
    # Group a full color and outer-sign period before extrapolation.
    N=a[1]
    def group(n):return sum(term(N*n+j) for j in range(N))
    return mp.nsum(group,[0,mp.inf],method='richardson',steps=[10,20,40,80])

def coeff_formula(a,b):
    def L(s,z):return mp.polylog(s,mp.exp(2j*mp.pi*z[0]/z[1]))
    def bj(k,z):
        if not z[0]%z[1] and k==1:return mp.mpf(0)
        return (2j*mp.pi)**k/mp.factorial(k)*mp.bernpoly(k,mp.mpf(z[0]%z[1])/z[1])
    c=neg(mul(a,b))
    return (-L(3,neg(a))-L(3,neg(b))-2*L(3,inv(a))-2*L(3,inv(b))-bj(3,c)
            -bj(1,c)*(L(2,inv(a))+L(2,inv(b))-L(2,neg(a))-L(2,neg(b)))
            -L(1,neg(b))*(bj(2,c)-bj(2,a))
            -L(1,neg(a))*(bj(2,c)-bj(2,b)))

if __name__=='__main__':
    cases=[((1,4),(1,4),'0.23','0.31'),
           ((1,4),(3,4),'0.17','0.17'),
           ((1,4),(0,4),'0.13','0.37'),
           ((0,4),(0,4),'0.19','0.27'),
           ((1,6),(2,6),'0.23','0.31')]
    results=[]
    for a,b,x,y in cases:
        x,y=mp.mpf(x),mp.mpf(y)
        lhs=direct(a,b,x,y)+direct(inv(a),inv(b),x,y)
        rhs=master(a,b,x,y)
        row={'a':a,'b':b,'x':str(x),'y':str(y),
             'lhs':mp.nstr(lhs,60),'rhs':mp.nstr(rhs,60),
             'absolute_error':mp.nstr(abs(lhs-rhs),6)}
        results.append(row); print(json.dumps(row),flush=True)
        assert abs(lhs-rhs) < mp.mpf('1e-50'),row
    (Path(__file__).resolve().parents[1] / 'data' / 'cyclotomic_verification.json').write_text(json.dumps(results,indent=2)+'\n')
