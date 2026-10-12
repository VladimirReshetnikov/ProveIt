"""Extra checks: arbitrary outer color, quarter-color square, Gamma primitive."""
import json
from pathlib import Path
import mpmath as mp
from verify_generator import F, B, inv, mul, tail

mp.mp.dps=60

def C(a,b,X,Y):
    c=mul(a,b)
    return ((B(c,X)*F(b,Y-X)-B(a,X)*F(b,Y))/X
            -(B(c,Y)*F(inv(a),Y-X)-F(inv(a),-X))/Y)

def Q(a,b,x,y):
    return (C(a,b,x,y)+C(a,b,x,-y)-C(a,b,-x,y)-C(a,b,-x,-y))/(4*x)

def J(c,x):
    if not c[0]%c[1]:return mp.mpf(0)
    theta=mp.mpf(c[0]%c[1])/c[1]
    if not x:return 1j*mp.pi*(2*theta-1)
    return 1j*mp.pi*mp.sin(mp.pi*(2*theta-1)*x)/mp.sin(mp.pi*x)

def master(a,b,c,x,y):
    d=mul(mul(a,b),c)
    jdd=(mp.diff(lambda t:J(d,t),x)/(2*x) if x==y
         else (J(d,x)-J(d,y))/(x*x-y*y))
    return Q(a,mul(b,c),x,y)+Q(b,mul(a,c),y,x)+jdd

def direct(a,b,c,x,y):
    N=a[1]
    omega=mp.exp(2j*mp.pi*c[0]/N)
    def term(n):
        return omega**n*(omega*(n+1)-n)*tail(a,x,n)*tail(b,y,n)
    return mp.nsum(lambda n:sum(term(N*n+j) for j in range(N)),
                   [0,mp.inf],method='richardson',steps=[10,20,40,80])

def Ominus(x):return (F((1,2),x)+F((1,2),-x))/2
def sine_rhs(x):
    if not x:return mp.pi**2*mp.log(2)/8
    return -mp.pi*mp.tan(mp.pi*x/2)*Ominus(x)/(4*x)

def sine_direct(x):
    def term(n):
        sine=(tail((1,4),x,n)-tail((3,4),x,n))/(2j)
        return (-1)**n*(2*n+1)*sine*sine
    return mp.nsum(lambda n:sum(term(4*n+j) for j in range(4)),
                   [0,mp.inf],method='richardson',steps=[10,20,40,80])

results=[]
def record(name,lhs,rhs):
    error=abs(lhs-rhs)
    row={'name':name,'lhs':mp.nstr(lhs,55),'rhs':mp.nstr(rhs,55),
         'absolute_error':mp.nstr(error,6)}
    results.append(row);print(json.dumps(row),flush=True)
    assert error < mp.mpf('1e-48'),row

for a,b,c in [((1,4),(0,4),(1,4)),((1,3),(2,3),(1,3)),
              ((0,4),(0,4),(0,4))]:
    x,y=mp.mpf('0.17'),mp.mpf('0.28')
    record('outer character '+str((a,b,c)),
           direct(a,b,c,x,y)+direct(inv(a),inv(b),inv(c),x,y),
           master(a,b,c,x,y))
for x in [mp.mpf(0),mp.mpf('0.25'),mp.mpf('0.5')]:
    record('quarter sine diagonal x='+str(x),sine_direct(x),sine_rhs(x))
u=mp.mpf('0.5')
record('anchored Gamma primitive',mp.quad(lambda x:-mp.pi*Ominus(x)/4,[0,u]),
       mp.pi/8*mp.log(mp.gamma(1+u/2)*mp.gamma((1-u)/2)/
                     (mp.gamma(1-u/2)*mp.gamma((1+u)/2))))
(Path(__file__).resolve().parents[1] / 'data' / 'cyclotomic_extra_verification.json').write_text(
    json.dumps(results,indent=2)+'\n')
