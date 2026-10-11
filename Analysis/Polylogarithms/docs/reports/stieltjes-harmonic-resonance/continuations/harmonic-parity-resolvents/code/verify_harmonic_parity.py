"""Exact finite checks and independent numerical diagnostics for centered harmonic parity.
Python 3; dependencies: sympy, mpmath. No tests assert an unproved zeta independence.
"""
from pathlib import Path
import argparse
import json
import sympy as sp
import mpmath as mp

parser=argparse.ArgumentParser()
parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results/latest/harmonic_parity_checks.json')
args=parser.parse_args()
args.output.parent.mkdir(parents=True,exist_ok=True)
z,L=sp.symbols('z L')
X=sp.symbols('X1:7')
Z={r:sp.Symbol(f'zeta{r}') for r in range(2,7)}
center=sp.Rational(1,2)
cut=17
psi=L-sum(sp.bernoulli(k,center)/k*z**k for k in range(1,cut))
def D(f):
    return -z**2*sp.diff(f,z)+z*sp.diff(f,L)
T={1:psi}
for r in range(2,7):
    h=psi
    for _ in range(r-1): h=D(h)
    T[r]=Z[r]-(-1)**r*sp.expand(h)/sp.factorial(r-1)
formal={X[r-1]:T[r] for r in range(1,7)}
tau={X[r-1]:2*Z[r]-X[r-1] for r in (2,4,6)}
cases={
 'H1_H3':X[0]*X[2],
 'tail2_square':(Z[2]-X[1])**2,
 'tail2_tail4':(Z[2]-X[1])*(Z[4]-X[3]),
 'H1_tail2_tail4':X[0]*(Z[2]-X[1])*(Z[4]-X[3]),
 'H2_raw':X[1],
 'tail2':Z[2]-X[1],
 'H1_tail2':X[0]*(Z[2]-X[1]),
 'tail2_cube':(Z[2]-X[1])**3,
}
exact={}
for name,P in cases.items():
    F=sp.expand(P.subs(formal))
    F=sp.Poly(F,z)
    coeff={int(k[0]):v for k,v in F.terms() if k[0]<cut}
    invariant=sp.expand(P-P.subs(tau,simultaneous=True))==0
    anti=sp.expand(P+P.subs(tau,simultaneous=True))==0
    even_ok=all(v==0 for k,v in coeff.items() if k%2)
    odd_ok=all(v==0 for k,v in coeff.items() if not k%2)
    if invariant: assert even_ok
    if anti: assert odd_ok
    exact[name]={'invariant':invariant,'anti_invariant':anti,
        'odd_coefficient_count_to_16':sum(1 for k,v in coeff.items() if k%2 and v!=0),
        'even_coefficient_count_to_16':sum(1 for k,v in coeff.items() if not k%2 and v!=0)}

# Compare the printed general-shift T_r formula with direct formal differentiation.
general_shift_checks=[]
for av in [sp.Rational(1,3),sp.Rational(7,5)]:
    psi_a=L-sum(sp.bernoulli(k,av)/k*z**k for k in range(1,13))
    for r in range(2,7):
        derived=psi_a
        for _ in range(r-1): derived=D(derived)
        derived=Z[r]-(-1)**r*derived/sp.factorial(r-1)
        printed=Z[r]-z**(r-1)/sp.Integer(r-1)-sum(
            sp.binomial(k+r-2,r-2)*sp.bernoulli(k,av)*z**(k+r-1)/sp.Integer(r-1)
            for k in range(1,13))
        assert sp.expand(derived-printed)==0
    general_shift_checks.append(str(av))

# Verify the Bernoulli centered shift equation for formal trigamma.
f=D(psi)
x=sp.symbols('x')
# Work in z: f(x+1)=f(z/(1+z)).
diff=sp.series(f.subs(z,z/(1+z))-f+z**2/(1+z/2)**2,z,0,15).removeO()
assert sp.expand(diff)==0

# Independently compute the finite-sum constant identities symbolically.
A=z-z**2/2+sum(sp.bernoulli(2*k)*z**(2*k+1) for k in range(1,12))
constant_checks={}
for j in range(1,9):
    power_sum=(sp.bernoulli(2*j,x+1)-sp.bernoulli(2*j))/(2*j)
    lhs1=sp.expand(A*power_sum.subs(x,1/z)).coeff(z,0)
    rhs1=sp.Rational(3-2*j,4)*sp.bernoulli(2*j-2)
    lhs2=sp.expand(A*A).coeff(z,2*j+1)
    rhs2=-sp.bernoulli(2*j-2)
    assert sp.simplify(lhs1-rhs1)==0
    assert sp.simplify(lhs2-rhs2)==0
    constant_checks[str(j)]={'A_times_power_sum':str(lhs1),'tail_square_boundary':str(lhs2)}

def exact_value(r):
    zeta3_coeff=3*sp.bernoulli(2*r,center)
    rational=-sp.Rational(1,2)*sum(sp.binomial(2*r,2*j)*sp.Rational(2*j-1,2*j+1)
           *sp.bernoulli(2*r-2*j,center)*sp.bernoulli(2*j-2) for j in range(1,r+1))
    return zeta3_coeff,rational

mp.mp.dps=110
def mprat(v):
    a,b=sp.fraction(v);return mp.mpf(str(a))/mp.mpf(str(b))
def predicted(r):
    a,b=exact_value(r);return mprat(a)*mp.zeta(3)+mprat(b)
def continuation(r,N,J):
    # Independent evaluation: finite direct trigamma sum and a tail obtained
    # from its Euler--Maclaurin expansion. This is a diagnostic, not enclosure.
    b=[sp.bernoulli(2*k,center) for k in range(J)]
    c=[sum(b[i]*b[k-i] for i in range(k+1)) for k in range(J)]
    direct=mp.fsum((mp.mpf(n)+mp.mpf('.5'))**(2*r)*mp.polygamma(1,n+1)**2
                   for n in range(N))
    tail=mp.fsum(mprat(c[k])*mp.zeta(2*k+2-2*r,mp.mpf(N)+mp.mpf('.5'))
                for k in range(J))
    return direct+tail
num={}
for r in range(7):
    a=continuation(r,64,38)
    b=continuation(r,96,45)
    wanted=predicted(r)
    err=abs(b-wanted); stable=abs(a-b)
    assert err < mp.mpf('1e-70')
    assert stable < mp.mpf('1e-65')
    ca,cb=exact_value(r)
    num[str(r)]={'zeta3_coefficient':str(ca),'rational_part':str(cb),
                'numerical_value':mp.nstr(b,60),'absolute_error':mp.nstr(err,8),
                'two_cutoff_difference':mp.nstr(stable,8)}

# Independent polylog expression vs exact Bernoulli moment series.
generator={}
for t in [mp.mpf('.2'),mp.mpf('.7'),mp.mpf('1.1')]:
    Q=mp.exp(-t)
    closed=t/(2*mp.sinh(t/2))*(2*mp.zeta(3)-t**3/48
              -t*mp.polylog(2,Q)/2-2*mp.polylog(3,Q)
              +3*(mp.zeta(4)-mp.polylog(4,Q))/t)
    series=mp.fsum(predicted(r)*t**(2*r)/mp.factorial(2*r) for r in range(62))
    integ=t/(2*mp.sinh(t/2))*(3*mp.zeta(3)-mp.quad(
        lambda u:(t-u)*u*u*mp.coth(u/2) if u else 0,[0,t])/(4*t))
    err=abs(closed-series); err2=abs(closed-integ)
    assert err < mp.mpf('1e-85')
    assert err2 < mp.mpf('1e-95')
    generator[mp.nstr(t)]={'closed_vs_moment_series_error':mp.nstr(err,8),
        'closed_vs_integral_error':mp.nstr(err2,8)}
result={'status':'all checks passed','exact_parity':exact,
        'general_shift_T_r_checks':general_shift_checks,'formal_trigamma_shift_equation_to_order':14,'finite_sum_constants':constant_checks,
        'centered_trigamma_square_values':num,'polylog_generator':generator,
        'precision_digits':mp.mp.dps,'tail_diagnostic_cutoffs': [{'N':64,'J':38},{'N':96,'J':45}],
        'qualification':'Numerical comparisons are diagnostics, not interval certificates; all assertions are proved in the accompanying TeX.'}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'checked_values':len(num),
    'worst_value_error':max(float(v['absolute_error']) for v in num.values()),
    'generator_points':len(generator)},indent=2))
