"""Independent algebraic/exact-arithmetic and floating-point audit, 2026-10-02.

The ODE calculation and fitted constants are numerical checks, not certificates.
The integer recurrence and polynomial identities are exact.
"""
import json, math, hashlib
from pathlib import Path
import os
from fractions import Fraction
import sympy as s
import mpmath as mp
from scipy.integrate import solve_ivp

P = Path(os.environ.get("HISTORIC_TREE_OUTPUT_DIR", Path(__file__).parent))
I = Path(os.environ.get("HISTORIC_TREE_INPUT_DIR", Path(__file__).parent / "originals"))
mp.mp.dps = 100
checks = {}
p,q,c,v=s.symbols('p q c v', positive=True)
qstar=4*c*c/3
pdot=q-4*p*p/3
qdot=1-5*p*q/3
vdot=5*(p-c)*pdot/3+(1-qstar/q)*qdot
claimed=-20*(p-c)**2*(p+c)/9-5*c*(q-qstar)**2/(3*q)
num=s.together(vdot-claimed).as_numer_denom()[0]
checks['lyapunov_derivative_exact']=s.rem(s.Poly(num,c),s.Poly(c**3-s.Rational(9,20),c)).is_zero
A=s.Matrix([[-8*c/3,1],[-5*qstar/3,-5*c/3]])
checks['jacobian_characteristic']=str(s.factor(A.charpoly(v).as_expr()))
lam=(13+s.sqrt(-71))/2
bar=(13-s.sqrt(-71))/2
D=lambda x:(3-x)*(4-x)*(5-x)-120
checks['indicial_factorization_exact']=s.simplify(D(v)+(v+1)*(v-lam)*(v-bar))==0
checks['a11']=str(s.simplify(s.Integer(120)/D(s.Integer(13))))
checks['a11_exact']=s.simplify(s.Integer(120)/D(s.Integer(13)))==s.Rational(-1,7)
checks['a20']=str(s.simplify(60/D(2*lam)))
checks['stirling_log_gamma_x_plus3_coefficient']=str(s.bernoulli(2,3)/2)

# Exact original h_n recurrence, with binomial coefficients updated multiplicatively.
N=600
h=[1,1,1]
for n in range(N-2):
    b,total=1,0
    for k in range(n+1):
        total+=b*h[k]*h[n-k]
        if k<n: b=b*(n-k)//(k+1)
    h.append(total)
expected=[1,1,1,1,2,4,8,18,48,144,456,1560,5808,23184,98160,440832,2101824,10588608,56104128,312013440,1818498816,11082682368,70467474816,466680045312,3214497245184,22994283345408,170573216656896,1310482565462016,10415453732637696]
checks['oeis_first29_exact']=h[:29]==expected
checks['producer_first30_exact']=h[:30]==json.loads((I/'numerics_150dps.json').read_text())['exact_first30']
data=''.join(f'{n} {a}\n' for n,a in enumerate(h))
(P/'exact_h_0_600.txt').write_text(data)
checks['exact_recurrence_nmax']=N
checks['exact_terms_sha256']=hashlib.sha256(data.encode()).hexdigest()

# Independent ordinary EGF Fraction recurrence; no reuse of the h recurrence.
b=[Fraction(1),Fraction(1),Fraction(1,2)]
for n in range(78):
    b.append(sum((b[k]*b[n-k] for k in range(n+1)),Fraction())/((n+1)*(n+2)*(n+3)))
checks['two_exact_recurrences_agree_through80']=all(b[n]*math.factorial(n)==h[n] for n in range(81))

def ode(t,Y):
    p,q,v,z=Y
    return [q-4*p*p/3,1-5*p*q/3,-p*v/3,v]
sol=solve_ivp(ode,[0,100],[1,1,1,0],rtol=2e-13,atol=2e-14,method='DOP853')
pstar=(9/20)**(1/3)
rho_ode=float(sol.y[3,-1]+3*sol.y[2,-1]/pstar)
checks['independent_double_precision_ode']={'success':bool(sol.success),'rho_approx':rho_ode,'p_final':float(sol.y[0,-1]),'q_final':float(sol.y[1,-1]),'not_certified':True}

# Check producer constants against independently computed exact integers.
producer=json.loads((I/'numerics_150dps.json').read_text())
rho=mp.mpf(producer['rho']); C=mp.mpc(producer['C_real'],producer['C_imag'])
la=(13+mp.sqrt(71)*1j)/2
K=2*C*rho**la/mp.gamma(3-la)
checks['producer_constants_against_independent_exact_terms']=[]
for n in [40,80,120,200,300,400,500,600]:
    ratio=mp.mpf(h[n])*rho**(n+3)/(30*mp.factorial(n+2))
    correction=2*mp.re(K*mp.gamma(n+3-la)/mp.gamma(n+3))
    checks['producer_constants_against_independent_exact_terms'].append({'n':n,'rho_ratio':mp.nstr((n+2)*mp.mpf(h[n-1])/h[n],35),'relative_main_error':mp.nstr(ratio-1,35),'relative_first_sector_error':mp.nstr(ratio-1-correction,35),'n13_times_first_sector_error':mp.nstr((ratio-1-correction)*n**13,35)})
checks['elementary_radius_bounds']={'lower':str(mp.root(180,4)),'upper':str(mp.root(60,3))}
checks['all_exact_boolean_checks_pass']=all(x for x in checks.values() if isinstance(x,bool))
(P/'independent_checks.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps(checks,indent=2))
