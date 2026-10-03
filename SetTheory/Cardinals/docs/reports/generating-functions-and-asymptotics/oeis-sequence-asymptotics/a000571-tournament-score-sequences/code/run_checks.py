#!/usr/bin/env python3
"""Replay exact, symbolic and non-interval numerical score-sequence checks.

Run from any working directory: python /path/to/scripts/run_checks.py
Requires the pinned packages in ../requirements.txt. No network access is used.
JSON and logs are written under ../results/. Numerical checks are diagnostics,
not interval-certified finite-n error bounds or substitutes for the proof.
"""
from pathlib import Path
import subprocess,sys,json,hashlib,math
import sympy as sp
ROOT=Path(__file__).resolve().parent.parent
SCRIPTS=ROOT/'scripts';OUT=ROOT/'results';OUT.mkdir(exist_ok=True)
names=['check_exact_counting.py','check_scores.py','check_crossover.py','check_higher_crossover.py','uniform_generator.py','check_weight_inverse.py']
for name in names:
 p=subprocess.run([sys.executable,str(SCRIPTS/name)],cwd=ROOT,capture_output=True,text=True)
 (OUT/(name+'.log')).write_text(p.stdout+p.stderr)
 if p.returncode:raise RuntimeError(f'{name} failed; see results/{name}.log')
# Exact symbolic local coefficients, independently from the numerical generator.
t,mu,e2,lam=sp.symbols('t mu e2 lam');tau=sp.symbols('tau')
A=-mu*t**2+sp.Rational(2,3)*t**3+e2*t**4+sp.Rational(8,15)*t**5+sp.Rational(46,105)*t**7
D=sp.series((sp.exp(-A)-1)/mu,t,0,5).removeO().expand()
ell=(mu**2/sp.Integer(2)-e2)/mu
assert sp.simplify(D.coeff(t,4)-ell)==0
assert D.coeff(t,2)==1 and D.coeff(t,3)==-sp.Rational(2,3)/mu
alpha=sp.symbols('alpha')
g1=alpha*(alpha+1)/2
g2=sp.expand((-(sp.bernoulli(3,-alpha)-sp.bernoulli(3,1))/6)+g1*g1/2)
fixed_symbolic=[]
for sig in [1,-1]:
 F=sp.series(sp.exp(sig*A),t,0,8).removeO().expand()*sig
 b=[F.coeff(t,j) for j in [3,5,7]]
 c1=sp.simplify(g1.subs(alpha,sp.Rational(3,2))-sp.Rational(5,2)*b[1]/b[0])
 c2=sp.simplify(g2.subs(alpha,sp.Rational(3,2))-sp.Rational(5,2)*b[1]/b[0]*g1.subs(alpha,sp.Rational(5,2))+sp.Rational(35,4)*b[2]/b[0])
 expected1=-sp.Rational(1,8)+sig*sp.Rational(5,2)*mu
 expected2=sp.Rational(1,128)+sp.Rational(35,8)*mu**2+sig*(sp.Rational(63,16)*mu+sp.Rational(35,4)*e2)
 assert sp.simplify(c1-expected1)==0
 assert sp.simplify(c2-expected2)==0
 fixed_symbolic.append({'sigma':sig,'c1':str(c1),'c2':str(c2)})
# Explicit inverse-Laplace polynomial rule for integer numerator exponents.
def laplace_integer(a,b):
 return sum(sp.binomial(a,j)*(-tau)**j/sp.factorial(b-a+j-1) for j in range(a+1) if b-a+j>=1)
k=sp.Rational(2,3)/mu
C2=sp.expand(laplace_integer(1,1)+laplace_integer(2,1)/2-ell*laplace_integer(2,2)+k*k*laplace_integer(3,3))
expectedC2=tau**2/2-tau-ell*(tau**2-2*tau)+k*k*(-3*tau+3*tau**2-tau**3/2)
assert sp.simplify(C2-expectedC2)==0
# Exact Landau data and independent OEIS prefixes.
landau=json.loads((OUT/'exact-counting-checks.json').read_text())
assert [row['S'] for row in landau]==[1,1,2,4,9,22,59,167,490,1486]
assert [row['I'] for row in landau]==[1,0,1,1,3,7,21,61,184,573]
fixed=json.loads((OUT/'score-checks.json').read_text())
higher=json.loads((OUT/'higher-crossover-checks.json').read_text())
# Non-interval diagnostic envelopes, deliberately not advertised as proof bounds.
assert abs(float(higher['ell'])-1.2256954272202659)<1e-14
for row in fixed['checks']:
 assert abs(float(row['score_scaled_second_residual'])-float(higher['fixed_score_c2']))<0.2
 assert abs(float(row['strong_scaled_second_residual'])-float(higher['fixed_strong_c2']))<0.3
cross=json.loads((OUT/'allorders-crossover-checks.json').read_text())
for row in cross['checks']:
 for M in [2,3,4]:
  assert abs(row[f'M{M}_scaled_residual'])<1.0
  assert row[f'M{M}_model']>0
 assert abs(row['actual']/row['M4_model']-1)<0.02
inv=json.loads((OUT/'weight-inverse-checks.json').read_text())
for row in inv:
 assert row['model_derivative']<0
 assert abs(row['scaled_tau_error'])<2.0
summary={'status':'PASS','exact_landau_max_n':10,'exact_recurrence_max_n':1000,
 'symbolic_fixed_coefficients':fixed_symbolic,'symbolic_d4':str(ell),
 'symbolic_C2_over_exp_minus_tau':str(sp.factor(C2)),
 'uniform_generator_orders':[0,1,2,3,4],
 'crossover_cases':len(cross['checks']),'inverse_cases':len(inv),
 'numerical_caveat':'Floating-point checks are non-interval diagnostics, not finite-n error certificates. The analytical theorem supplies asymptotic error bounds.',
 'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(SCRIPTS.glob('*.py'))}}
(OUT/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(f"PASS: exact Landau/renewal identities, symbolic coefficients, {len(cross['checks'])} crossover cases through M4, and {len(inv)} inverse cases")
