"""Exact symbolic circle and independently parameterized chord checks."""
import json
from pathlib import Path
import sympy as s

h,y=s.symbols('h y')
k=s.symbols('k',positive=True)
z=s.symbols('z')
I=s.I

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def equal(a,b,message):
    require(s.simplify(a-b)==0,message)

def exp_coefficients(phase,degree):
    # If E=exp(S), then j E_j=sum_{l=1}^j l S_l E_{j-l}.
    E=[s.Integer(1)]
    for j in range(1,degree+1):
        E.append(s.expand(sum(l*phase.coeff(h,l)*E[j-l]
                              for l in range(1,j+1))/j))
    return E

def mean(poly,variance):
    ans=0
    for (j,),v in s.Poly(poly,y).terms():
        if j%2==0:
            ans+=v*s.factorial2(j-1)*variance**(j//2)
    return s.factor(ans)

S=(k*(s.exp(I*h*y)+2*s.exp(-I*h*y/2)-3)/h**2+3*k*y*y/4+I*h*y
   +h**2*k*k/2*(s.exp(2*I*h*y)-z*s.exp(I*h*y/2))
   +h**4*k*(1+z/2)*s.exp(I*h*y))
S=s.series(S,h,0,5).removeO().expand()
E=exp_coefficients(S,4)
expected=[s.Integer(1),k*k*(1-z)/2-s.Rational(5,36)/k,
          k**4*(1-z)**2/8+k*(53*z-17)/72-s.Rational(35,2592)/k**2]
circle=[mean(E[2*j],s.Rational(2,3)/k) for j in range(3)]
for j in range(3):
    equal(circle[j],expected[j],f'Circle c{j} mismatch')
for j in range(1,5):
    equal(S.coeff(h,j).subs(y,-y),(-1)**j*S.coeff(h,j),f'S parity {j}')
for j in (1,3):
    equal(mean(E[j],s.Rational(2,3)/k),0,f'Odd moment {j}')

# A genuinely different local coordinate, u=k*h^4+i*sqrt(2k/3)*h^5*y.
gamma=s.sqrt(2*k/3)
r=1+I*gamma*h*y/k
R=(2*k*(r**(-s.Rational(1,2))-1)/h**2+k*(r-1)/h**2+y*y/2
   +h*h*k*k/2*(r*r-z*s.sqrt(r))+k*(1+z/2)*h**4*r)
R=s.series(R,h,0,5).removeO().expand()
chord_exp=exp_coefficients(R,4)
chord=[mean(chord_exp[2*j],s.Integer(1)) for j in range(3)]
for j in range(3):
    equal(chord[j],circle[j],f'Independent chord c{j} mismatch')

# Exact leading monodromy numerator identity behind odd local strength.
a,v=s.symbols('a v')
equal(((-3*a-s.pi/2)*(-v))-(3*a-s.pi/2)*v,s.pi*v,
      'Odd-shift exponent mismatch')

result={'status':'pass','sympy_version':s.__version__,
        'circle_and_chord_agree_through':2,
        'odd_moments_vanish_through_h_degree':3,
        'coefficients':[str(s.factor(c)) for c in circle]}
Path('checks').mkdir(exist_ok=True)
Path('checks/symbolic_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
