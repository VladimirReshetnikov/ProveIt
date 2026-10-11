#!/usr/bin/env python3
"""Finite exact checks; the arbitrary-index analytic proofs are in article.tex."""
import itertools,json,math,sys
from pathlib import Path
import sympy as S
from sympy.functions.combinatorial.numbers import stirling
ROOT=Path(__file__).resolve().parents[1]
z,x,R=S.symbols('z x R')
counts={}; tables={}
def check(group,condition):
    if not condition: raise AssertionError(group)
    counts[group]=counts.get(group,0)+1
# Stirling/Pochhammer compiler, independent polynomial differentiation.
for k in range(10):
    poly=S.Poly(S.rf(x,k),x)
    for q in range(8):
        st=stirling(k,q,kind=1,signed=False) if q<=k else S.Integer(0)
        check('stirling_derivatives',S.diff(poly.as_expr(),x,q).subs(x,0)==math.factorial(q)*st)
# The jump of a product of logs, compared with its odd-multinomial formula.
logs=S.symbols('l0:3');P=S.symbols('P',real=True)
for qs in itertools.product(range(4),repeat=3):
    for flags in [(1,0,0),(1,1,0),(1,1,1)]:
        plus=S.prod((l+S.I*P*f)**q for l,q,f in zip(logs,qs,flags))
        minus=S.prod((l-S.I*P*f)**q for l,q,f in zip(logs,qs,flags))
        direct=S.expand((plus-minus)/(2*S.I))
        explicit=0
        for ks in itertools.product(*[range(q+1) for q in qs]):
            K=sum(ks)
            if K%2:
                explicit+=(-1)**((K-1)//2)*P**K*S.prod(
                    S.binomial(q,k)*l**(q-k)*f**k for l,q,k,f in zip(logs,qs,ks,flags))
        check('mixed_cut_polynomials',S.expand(direct-explicit)==0)
# Derivative-residue polynomials, independently generated from secant/cotangent translation.
Pn=S.Integer(1); polys=[]
t=S.symbols('t')
N=7
u=S.series(S.cos(t)-1-z*S.sin(t),t,0,N).removeO()
series=0
for k in range(N):
    series+=(-1)**k*S.rf(R,k)/S.factorial(k)*S.series(u**k,t,0,N).removeO()
series=S.Poly(S.expand(series),t)
for n in range(N):
    if n: Pn=S.expand(R*z*Pn+(1+z*z)*S.diff(Pn,z))
    check('residue_polynomials',S.expand(series.coeff_monomial(t**n)*S.factorial(n)-Pn)==0)
    polys.append(str(Pn))
tables['residue_polynomials']=polys
# Logarithmic cumulants: independent Taylor expansion of the analytic germ.
maxq=7
for odd in (True,False):
    trig=S.sin(S.pi*x/2)/(S.pi*x/2) if odd else S.cos(S.pi*x/2)
    trlog=S.series(S.log(trig),x,0,maxq).removeO()
    for n in range(7):
        logg=S.EulerGamma*x+sum(S.zeta(k)*x**k/k for k in range(2,maxq))+trlog
        logg-=sum(S.series(S.log(1+x/j),x,0,maxq).removeO() for j in range(1,n+1))
        for k in range(1,maxq):
            H=S.harmonic(n,k)
            if k==1: expected=S.EulerGamma-H
            else:
                corr=(S.Integer(2)**(1-k) if odd else 2*(1-S.Integer(2)**(-k))) if k%2==0 else 0
                expected=S.factorial(k-1)*((1-corr)*S.zeta(k)+(-1)**k*H)
            actual=S.expand(logg).coeff(x,k)*S.factorial(k)
            check('spectral_cumulants',S.simplify(actual-expected)==0)
# Contact coefficients from the actual sine quotient (same finite-part scale).
for m in range(1,9):
    germ=2*S.I**(m-1)/S.factorial(m-1)*S.series(S.sin(S.pi*x/2)/x,x,0,11).removeO()
    for q in range(10):
        expected=0 if q%2 else S.pi*S.I**(m-1)/S.factorial(m-1)*(-1)**(q//2)*(S.pi/2)**q/(q+1)
        actual=S.expand(germ).coeff(x,q)*S.factorial(q)
        check('contact_jets',S.simplify(actual-expected)==0)
# Anchor primitive denominator including resonances.
for k in range(1,9):
    check('primitive_denominators',S.expand((-1)**k*S.rf(x-k,k)-S.rf(1-x,k))==0)
    for m in range(1,k+1):
        check('simple_resonance_roots',S.diff(S.rf(1-x,k),x).subs(x,m)!=0)
# Negative controls are deliberate incorrect formulas and must be rejected.
check('negative_controls',S.expand((logs[0]+S.I*P)*(logs[1]+S.I*P)*(logs[2]+S.I*P)-
    (logs[0]-S.I*P)*(logs[1]-S.I*P)*(logs[2]-S.I*P)-2*S.I*P*(logs[0]*logs[1]+logs[0]*logs[2]+logs[1]*logs[2]))!=0)
check('negative_controls',S.pi/2!=0) # omitted half residue at a simple centered pole
check('negative_controls',S.simplify(S.pi*(S.pi/2)**2/3-(-S.pi*(S.pi/2)**2/3))!=0)
report={'status':'PASS','exact_assertions':sum(counts.values()),'groups':counts,
        'sympy_version':S.__version__,'tables':tables,
        'meaning':'Finite symbolic consistency checks; not a proof-assistant certificate.'}
(ROOT/'data/exact_results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='tables'},indent=2))
