"""Exact arithmetic behind the four displayed spectral integrals.
No numerical recognition is used: Riemann-zeta derivatives are formal symbols.
Also checks the low-b rational square coefficients and partial fractions.
"""
from pathlib import Path
import json
import sympy as s

HERE = Path(__file__).resolve().parent
v, X = s.symbols('v X')
L = s.log(2)
P = (1-v*v)**3

def zp(j): return s.Symbol(f'Zp{j}')
def zpp(j): return s.Symbol(f'Zpp{j}')

def psi_endpoint(poly):
    result = s.S.Zero
    for j in range(s.degree(poly,v)+1):
        a = s.diff(poly,v,j).subs(v,1)
        b = s.diff(poly,v,j).subs(v,-1)
        z = s.zeta(-j)
        result += (-1)**j/s.factorial(j)*(a*(zp(j)+2**j*L+s.harmonic(j)*(z-1-2**j))-b*(zp(j)+s.harmonic(j)*z))
    return s.expand(result)

expected = [16*zp(3)+12*zp(5)+s.Rational(2,7),
            64*zp(3)+240*zp(5)+48*zp(7)+s.Rational(547,1800),
            -112*zp(4)-140*zp(6)-18*zp(8)+s.Rational(32,105)]
for poly, target in zip([P,P*(1+3*v*v),P*(v+v**3)],expected):
    assert s.simplify(psi_endpoint(poly)-target)==0

gamma1=s.S.Zero
for j in range(7):
    a=s.diff(P,v,j).subs(v,1);b=s.diff(P,v,j).subs(v,-1)
    H=s.harmonic(j);eta2=(H**2+s.harmonic(j,2))/2
    z=s.zeta(-j)
    gamma1+=(-1)**j/s.factorial(j)*(a*((zpp(j)-2**j*L**2)/2+H*(zp(j)+2**j*L)+eta2*(z-1-2**j))-b*(zpp(j)/2+H*zp(j)+eta2*z))
target=8*zpp(3)+6*zpp(5)+s.Rational(88,3)*zp(3)+s.Rational(137,5)*zp(5)-s.Rational(16,15)*L+s.Rational(521,900)
assert s.simplify(s.expand(gamma1-target))==0

G=[-1/(384*(X+1)*(X+3)*(X+5)*(X+7)),
   -1/(2304*(X+1)*(X+5)*(X+7)*(X+9)),
   -(X+2)*(X+6)/(27648*s.prod(X+2*j+1 for j in range(6))),
   -(X**3+15*X**2+62*X+63)/(497664*s.prod(X+2*j+1 for j in range(7)))]
for b,g in enumerate(G):
    beta=-sum(s.binomial(b,j)*3**j/s.prod(X+2*j+2*r+1 for r in range(4)) for j in range(b+1))/(384*s.factorial(b)*24**b)
    assert s.cancel(beta-g)==0
x,c=s.symbols('x c')
for m in range(1,13):
    pf=sum((-1)**(m-r)/(c**(m-r+1)*x**r) for r in range(1,m+1))+(-1)**m/(c**m*(x+c))
    assert s.cancel(pf-1/(x**m*(x+c)))==0

# Check the explicitly printed H8 and N11 against the exact certificates.
u=s.symbols('u0:12')
H8=-4*u[0]**7+56*u[0]**5*u[1]-70*u[0]**4*u[2]-140*u[0]**3*u[1]**2+56*u[0]**3*u[3]+252*u[0]**2*u[1]*u[2]-28*u[0]**2*u[4]+112*u[0]*u[1]**3-112*u[0]*u[1]*u[3]-84*u[0]*u[2]**2+8*u[0]*u[5]-98*u[1]**2*u[2]+20*u[1]*u[4]+36*u[2]*u[3]-u[6]
N11=u[0]**11-330*u[0]**7*u[1]**2+462*u[0]**5*u[2]**2-1155*u[0]**3*u[1]**4-165*u[0]**3*u[3]**2+550*u[0]**2*u[2]**3+990*u[0]*u[1]**2*u[2]**2+11*u[0]*u[4]**2-55*u[2]*u[3]**2
records=json.loads((HERE/'normal_form_certificates.json').read_text())
def from_record(poly):
    return s.expand(sum(s.Rational(coeff)*s.prod(u[j]**int(a) for j,a in enumerate(key.split(','))) for key,coeff in poly.items()))
assert s.expand(H8-from_record(records['8']['H']))==0
assert s.expand(N11-from_record(records['11']['N']))==0
result={"status":"PASS","exact_spectral_integrals":4,"rational_coefficient_families":4,
        "partial_fraction_checks":12,"printed_normal_form_and_primitive_checks":2,
        "scope":"Exact symbolic consequences, not proof-assistant certification"}
(HERE/'endpoint_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
