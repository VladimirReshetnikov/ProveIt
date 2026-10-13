"""Exact support checks for the analytic consecutive-tail exclusion theorem.

The universal argument is in consecutive-exclusion.tex; this finite checker
does not replace its interlacing and angular estimates. It independently
reconstructs numerators by Stirling sums, verifies shift identities, replays
the existing finite Bezout certificate needed for the strip 0<a<=7, and
checks the exact rational constants and wrong-formula controls.
"""
from pathlib import Path
from math import factorial
import argparse
import hashlib
import importlib.util
import json
import platform
import sys
import time
import sympy as s
from sympy.functions.combinatorial.numbers import stirling

HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'.git').exists())
CANONICAL=ROOT/'Analysis/Polylogarithms/docs/manuscript/verification'
a,w=s.symbols('a w',real=True)

def require(condition,message):
    if not bool(condition):raise ValueError(message)

def normhash(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')).hexdigest()

def default(name):
    local=HERE/name
    return local if local.exists() else CANONICAL/name

def checks():
    out=[]
    def check(name,condition):
        require(condition,name)
        out.append({'name':name,'pass':True})
    # Independent finite Stirling expansion of (n+a)^k, rather than the recurrence.
    P=[]
    recurrence=s.Integer(1)
    for k in range(10):
        closed=s.expand(sum(s.binomial(k,j)*a**(k-j)*stirling(j,i,kind=2)*factorial(i)
                            *w**i*(1-w)**(k-i) for j in range(k+1) for i in range(j+1)))
        P.append(closed)
        check(f'Stirling numerator equals differential recurrence k={k}',closed==recurrence)
        check(f'Positive base constant coefficient k={k}',s.expand(closed.subs(w,0)-a**k)==0)
        check(f'Base leading coefficient k={k}',s.expand(s.Poly(closed,w).nth(k)-(1-a)**k)==0)
        if k>=1:
            boundary=s.Poly(closed.subs(a,1),w)
            check(f'Boundary b=1 degree and positive leading coefficient k={k}',
                  boundary.degree()==k-1 and boundary.LC()==1)
        recurrence=s.expand(w*(1-w)*s.diff(recurrence,w)+(a+(k+1-a)*w)*recurrence)
    for k in range(9):
        for n in range(1,7):
            shift=sum((a+j)**k*w**j for j in range(n))
            residual=s.expand(w**n*P[k].subs(a,a+n)-P[k]+(1-w)**(k+1)*shift)
            check(f'Exact finite shift identity k={k}, n={n}',residual==0)
        derivative=s.expand(w*(1-w)*s.diff(P[k],w)+(k+1)*w*P[k]
                            -P[k+1]+a*(1-w)*P[k])
        check(f'Color derivative identity k={k}',derivative==0)
    # Small exact Sturm diagnostics illustrate, but do not prove, the universal lemma.
    for b in (s.Rational(1,4),s.Rational(1,2),s.Rational(3,4),s.Integer(1)):
        for k in range(1,9):
            poly=s.Poly(P[k].subs(a,b),w)
            check(f'Finite simple-negative-root diagnostic k={k}, b={b}',
                  s.gcd(poly,poly.diff()).degree()==0 and poly.count_roots(-s.oo,0)==poly.degree())
    rho=s.Rational(5,6)**8
    margin=9*(1-rho)**2-20*rho
    check('Exact n=6,k=8 margin identity',margin==s.Rational(1831480182729,2821109907456))
    check('Exact n=6,k=8 margin is positive',margin>0)
    taylor=sum(s.Rational(3,2)**j/s.factorial(j) for j in range(7))
    check('Seven Taylor terms prove exp(3/2)>40/9',taylor>s.Rational(40,9))
    check('Linear-region rational angular constant',
          s.Rational(8,3)*s.Rational(9,40)/(1-s.Rational(9,40))**2==s.Rational(960,961))
    # Domain-sensitive small checks of the angular identities and root-disc scaling.
    omega=s.Rational(3,5)+s.Rational(4,5)*s.I
    for r in (s.Rational(1,3),s.Integer(1),s.Integer(4)):
        expected=r*s.Rational(4,5)/s.expand((omega+r)*(s.conjugate(omega)+r))
        check(f'Negative-root angular identity r={r}',s.simplify(s.im(omega/(omega+r))-expected)==0)
    check('Pole angular contribution has the positive sign',s.im(omega/(1-omega))==1)
    check('Unit-circle pole denominator is less than four',s.expand((1-omega)*(1-s.conjugate(omega)))<4)
    for k,n,b in ((8,6,s.Integer(1)),(3,4,s.Rational(1,3)),(1,2,s.Rational(1,2))):
        radius=((b+n-2)/(b+n-1))**k
        scaled=[(b+j)**k*radius**j for j in range(n)]
        check(f'Enestrom scaling coefficients are nondecreasing k={k},n={n},b={b}',
              all(scaled[j]>=scaled[j-1] for j in range(1,n)))
    # These deliberately incorrect formulas must fail exact equality.
    controls=[]
    def reject(name,residual):
        require(s.expand(residual)!=0,'Accepted wrong formula: '+name)
        controls.append({'name':name,'rejected':True,'exact_residual':str(s.expand(residual))})
    k,n,b=2,2,s.Rational(1,3)
    S=sum((b+j)**k*w**j for j in range(n))
    reject('Wrong sign of finite shift sum',w**n*P[k].subs(a,b+n)-P[k].subs(a,b)-(1-w)**(k+1)*S)
    reject('Wrong shift prefactor',w**(n+1)*P[k].subs(a,b+n)-P[k].subs(a,b)+(1-w)**(k+1)*S)
    reject('Wrong pole imaginary sign',s.im(omega/(1-omega))+1)
    reject('Dropped factor four in the linear angular constant',
           s.Rational(2,3)*s.Rational(9,40)/(1-s.Rational(9,40))**2-s.Rational(960,961))
    return {'exact_checks':out,'exact_check_count':len(out),'negative_controls':controls,
            'negative_control_count':len(controls),'uniform_strip_margin':str(margin),
            'exp_three_halves_Taylor_lower_bound':str(taylor)}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--finite-certificates',type=Path,default=default('stieltjes-unit-circle-certificates.json'))
    parser.add_argument('--finite-verifier',type=Path,default=default('check_stieltjes_unit_circle.py'))
    parser.add_argument('--output',type=Path,default=HERE/'stieltjes-consecutive-exclusion.json')
    args=parser.parse_args()
    started=time.monotonic()
    metadata={'schema_version':1,'status':'RUNNING','python':platform.python_version(),
              'sympy':s.__version__,'optimization_level':sys.flags.optimize,
              'script_sha256_lf':normhash(Path(__file__)),
              'finite_verifier_sha256_lf':normhash(args.finite_verifier),
              'finite_certificates_sha256_lf':normhash(args.finite_certificates)}
    inputs=(Path(__file__).resolve(),args.finite_verifier.resolve(),args.finite_certificates.resolve())
    require(args.output.resolve() not in inputs,'Output must not overwrite an input')
    if args.output.exists():
        require(not any(args.output.samefile(p) for p in inputs),'Output must not alias an input')
    def write(value):args.output.write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8')
    write(metadata)
    try:
        own=checks()
        sys.dont_write_bytecode=True
        spec=importlib.util.spec_from_file_location('published_finite_circle',args.finite_verifier)
        finite=importlib.util.module_from_spec(spec)
        spec.loader.exec_module(finite)
        payload=json.loads(args.finite_certificates.read_text(encoding='utf-8'))
        earlier,_=finite.verify_payload(payload)
        require(len(earlier)==41,'Unexpected prior finite-check count')
        result={**metadata,**own,'status':'PASS','replayed_finite_check_count':len(earlier),
                'replayed_finite_checks':earlier,'elapsed_seconds':round(time.monotonic()-started,3),
                'evidence_boundary':'Universal analytic proof is separate. Finite checks verify supporting identities, the exact boundary constants, and the existing order-eight Bezout certificates. No numerical roots or broad sweep.'}
        write(result)
        print('PASS:',own['exact_check_count'],'new exact checks,',len(earlier),'replayed finite checks,',
              own['negative_control_count'],'rejected wrong formulas',flush=True)
        return 0
    except Exception as exc:
        write({**metadata,'status':'FAIL','error':f'{type(exc).__name__}: {exc}'})
        print('FAIL:',exc,file=sys.stderr)
        return 1

if __name__=='__main__':sys.exit(main())
