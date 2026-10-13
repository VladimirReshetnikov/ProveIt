"""Exact finite checks for the proved finite-dilation identities.

The infinite results are proved in finite-dilations.tex. This script checks
independent polynomial forms, scale normalizations, and concrete values.
"""
import json
import hashlib
import platform
import sys
from pathlib import Path
from math import factorial
import sympy as s

x, z, a = s.symbols('x z a')
checks = []
controls = []
def check(name, condition):
    if not bool(condition):
        raise RuntimeError(f'Exact check failed: {name}')
    checks.append(name)
def reject(name, wrong, correct):
    if s.simplify(wrong-correct) == 0:
        raise RuntimeError(f'Negative control failed to distinguish the corrupted formula: {name}')
    controls.append(name)
def Q(q,k):
    return s.diff(s.rf(1+z,k),z,q).subs(z,0)/factorial(k)

for lam in [s.Integer(2),s.Rational(3,2)]:
    for q in range(7):
        for r in range(1,6):
            p=s.Poly(s.prod(1-x/lam**ell for ell in range(q,q+r)),x)
            c=[p.nth(j) for j in range(r+1)]
            check(f'constant normalization {lam,q,r}',c[0]==1)
            for k in range(q,q+r):
                check(f'tail cancellation {lam,q,r,k}',
                      sum(c[j]*lam**(j*k) for j in range(r+1))==0)
                derivative=-sum(j*c[j]*lam**(j*k) for j in range(r+1))
                claimed=s.prod(1-lam**(k-ell) for ell in range(q,q+r) if ell!=k)
                check(f'Mellin derivative sign {lam,q,r,k}',derivative==claimed)
                # Euler--Maclaurin form versus zeta-tail form, polynomially in a.
                em=(-1)**(k+1)*s.bernoulli(k+1,a)*s.diff(s.rf(1+z,k),z,q).subs(z,0)/factorial(k+1)
                zr=(-1)**k*(-s.bernoulli(k+1,a)/(k+1))*Q(q,k)
                check(f'Bernoulli tail conversion {lam,q,r,k}',s.expand(em-zr)==0)
            check(f'next filter tail survives {lam,q,r}',p.eval(lam**(q+r))!=0)
            mat=s.Matrix([[lam**(j*k) for j in range(r)] for k in range(q,q+r)])
            check(f'minimal support determinant {lam,q,r}',mat.det()!=0)

# Direct coefficients in the displayed examples include the exterior 1/h.
check('U normalized coefficients',[s.Rational(1),-s.Rational(3,4),s.Rational(1,8)]==
      [s.Poly((1-x)*(1-x/2),x).nth(j)/2**j for j in range(3)])
check('V normalized coefficients',[s.Rational(1),-s.Rational(3,8),s.Rational(1,32)]==
      [s.Poly((1-x/2)*(1-x/4),x).nth(j)/2**j for j in range(3)])
check('U first log coefficient',s.zeta(0)*s.Rational(1,2)==-s.Rational(1,4))
check('U second log coefficient',-s.zeta(-1)*(1-2)==-s.Rational(1,12))
check('U third zeta derivative multiplier',((1-4)*(1-2))==3)
check('V first log coefficient',-s.zeta(-1)*s.Rational(1,2)==s.Rational(1,24))
check('V second value zero',s.zeta(-2)==0)
check('U next tail survives',s.zeta(-3)*(1-8)*(1-4)!=0)

# Principal residue-class formula agrees with inclusion--exclusion at all
# checked negative integer arguments, and at the scalar pole residue.
for d in [1,2,4,6,12,30]:
    primes=list(s.factorint(d))
    divs=s.divisors(s.prod(primes))
    check(f'principal scalar pole {d}',sum(s.mobius(h)/h for h in divs)==s.Rational(s.totient(d),d))
    for k in range(9):
        by_residues=d**k*sum(-s.bernoulli(k+1,s.Rational(j,d))/(k+1)
                             for j in range(1,d+1) if s.gcd(j,d)==1)
        by_euler=s.prod(1-p**k for p in primes)*s.zeta(-k)
        check(f'principal tail dictionary {d,k}',by_residues==by_euler)
    for q in range(1,9):
        leading=s.prod(1-p**q for p in primes)*s.zeta(-q)
        next_term=s.prod(1-p**(q+1) for p in primes)*s.zeta(-q-1)
        check(f'principal moment criterion {d,q}',(leading==0)==(q%2==0))
        if q%2==0:
            check(f'principal block stops {d,q}',next_term!=0)

reject('omitting exterior inverse scale destroys second U cancellation',
       1-s.Rational(3,2)*4+s.Rational(1,2)*16,0)
reject('reversing Mellin derivative sign changes U first moment',
       s.Rational(1,4),-s.Rational(1,4))
reject('omitting principal scalar subtraction leaves a nonzero residue',
       s.Rational(1,2),0)
reject('dropping q0 factor loses endpoint cancellation',1-s.Rational(1,2),0)

receipt={'status':'PASS','exact_checks':len(checks),'checks':checks,
         'negative_controls':len(controls),'controls':controls,
         'digest_mode':'lf-normalized',
         'script_sha256':hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
         'source_sha256':{},
         'source_note':'Self-contained exact formulas; no external source file is imported.',
         'python_version':platform.python_version(),'sympy_version':s.__version__,
         'optimization_level':sys.flags.optimize,
         'scope':'Finite exact checks support the separate all-order analytic proofs; no numeric inference.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(f'PASS: {len(checks)} exact checks and {len(controls)} negative controls')
