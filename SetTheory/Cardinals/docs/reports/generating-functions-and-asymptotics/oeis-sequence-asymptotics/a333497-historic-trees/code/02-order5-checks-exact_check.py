#!/usr/bin/env python3
"""Exact finite algebraic checks. This is not a proof of analytic continuation.

No check depends on Python assert, floating-point equality, network access,
private files, or the working directory. Rational quadratic arithmetic is exact.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import re
import sys
import sympy as s

ROOT = Path(__file__).resolve().parent
class VerificationError(Exception):
    pass

def require(condition, code, detail):
    if not condition:
        raise VerificationError(f'{code}: {detail}')

def strict_object(pairs):
    out = {}
    for key, val in pairs:
        require(key not in out, 'SCHEMA_DUPLICATE', f'duplicate key {key}')
        out[key] = val
    return out

def rational(v):
    require(type(v) is str and re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?', v),
            'SCHEMA_RATIONAL', f'invalid rational {v!r}')
    value = F(v)
    require(str(value) == v, 'SCHEMA_RATIONAL', f'noncanonical rational {v!r}')
    return value

KEYS = {'schema_version','sequence_id','max_n','display_terms','initial_values',
        'pole_coefficient','factorial_coefficient','normalized_flow','lyapunov_coefficients',
        'fowler_coefficients','alpha','D_coefficients_ascending','denominator_lower_bound',
        'catalan_M','psi_degree','a20','a11','transfer_relative_multiplier',
        'stirling_correction_ascending','second_stirling_correction_ascending','lambert_second_correction','inverse_epsilon_order'}
LENGTHS = {'display_terms':29, 'initial_values':3, 'normalized_flow':2,
           'lyapunov_coefficients':3, 'fowler_coefficients':5, 'alpha':2,
           'D_coefficients_ascending':4, 'a20':2, 'a11':2,
           'stirling_correction_ascending':3, 'second_stirling_correction_ascending':5, 'lambert_second_correction':3}
SCALARS = {'pole_coefficient','factorial_coefficient','denominator_lower_bound',
           'catalan_M','transfer_relative_multiplier'}

def load_fixture(path):
    try:
        f = json.loads(path.read_text(), object_pairs_hook=strict_object)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f'SCHEMA_JSON: {exc}') from exc
    require(type(f) is dict and set(f) == KEYS, 'SCHEMA_KEYS', 'exact top-level keys required')
    for key, value in [('schema_version',1),('max_n',500),('psi_degree',8),('inverse_epsilon_order',5)]:
        require(type(f[key]) is int and f[key] == value, 'SCHEMA_PARAMETER', f'{key} must equal {value}')
    require(f['sequence_id'] == 'A333497', 'SCHEMA_SEQUENCE', 'wrong sequence identifier')
    for key, length in LENGTHS.items():
        require(type(f[key]) is list and len(f[key]) == length,
                'SCHEMA_LENGTH', f'{key} must have {length} entries')
        f[key] = [rational(x) for x in f[key]]
    for key in SCALARS:
        f[key] = rational(f[key])
    require(all(x.denominator == 1 and x > 0 for x in f['display_terms']),
            'SCHEMA_TERM', 'display terms must be positive integers')
    return f

@dataclass(frozen=True)
class K:
    """a+b*j, j^2=-71, with exact rational a,b."""
    a: F = F(0)
    b: F = F(0)
    def __post_init__(self):
        object.__setattr__(self, 'a', F(self.a))
        object.__setattr__(self, 'b', F(self.b))
    @staticmethod
    def cast(x):
        return x if isinstance(x, K) else K(x)
    def __add__(self, other):
        other=K.cast(other); return K(self.a+other.a,self.b+other.b)
    __radd__=__add__
    def __neg__(self): return K(-self.a,-self.b)
    def __sub__(self, other): return self+-K.cast(other)
    def __rsub__(self, other): return K.cast(other)+-self
    def __mul__(self, other):
        other=K.cast(other)
        return K(self.a*other.a-71*self.b*other.b,self.a*other.b+self.b*other.a)
    __rmul__=__mul__
    def conjugate(self): return K(self.a,-self.b)
    def norm2(self): return self.a*self.a+71*self.b*self.b
    def __truediv__(self, other):
        other=K.cast(other)
        require(other.norm2()!=0, 'ZERO_DENOMINATOR', 'quadratic-field division by zero')
        p=self*other.conjugate(); n=other.norm2(); return K(p.a/n,p.b/n)
    def __pow__(self,n):
        require(type(n) is int and n>=0, 'ARITHMETIC_POWER', 'nonnegative integer power required')
        out=K(1)
        for _ in range(n): out=out*self
        return out
    def record(self): return [str(self.a),str(self.b)]

def integer_terms(max_n=500):
    h=[1,1,1]
    for n in range(max_n-2):
        h.append(sum(comb(n,k)*h[k]*h[n-k] for k in range(n+1)))
    return h

def terms_text(h): return ''.join(f'{n} {v}\n' for n,v in enumerate(h))
def poly_eval(coeff,b): return sum(c*b**j for j,c in enumerate(coeff))
def zero(expr, code, detail): require(s.cancel(s.expand(expr))==0,code,detail)
def sr(x): return s.Rational(x.numerator,x.denominator)

def parse_bfile(path):
    pairs=[]
    try: text=path.read_text()
    except (OSError, UnicodeError) as exc:
        raise VerificationError(f'TERMS_READ: {exc}') from exc
    for line in text.splitlines():
        if not line.strip() or line.lstrip().startswith('#'): continue
        require(re.fullmatch(r'(?:0|[1-9][0-9]*) [1-9][0-9]*',line) is not None,
                'BFILE_FORMAT', 'expected canonical index, one space, positive integer')
        n,v=map(int,line.split()); pairs.append((n,v))
    require([n for n,_ in pairs]==list(range(501)), 'BFILE_INDEX', 'expected every index 0..500 exactly once')
    return [v for _,v in pairs]

def run(f, bfile=None, terms_file=None):
    checks=[]
    def passed(name): checks.append(name)
    h=integer_terms(f['max_n'])
    require(f['initial_values']==list(map(F,h[:3])), 'INITIAL_VALUES', 'h0,h1,h2 must equal 1')
    require(f['display_terms']==list(map(F,h[:29])), 'OEIS_DISPLAY', 'a displayed OEIS term differs from recurrence')
    # An independent ordinary-coefficient recurrence; no binomial coefficients.
    egf=[F(1),F(1),F(1,2)]
    for n in range(78):
        egf.append(sum(egf[k]*egf[n-k] for k in range(n+1))/((n+1)*(n+2)*(n+3)))
    require(all(egf[n]*factorial(n)==h[n] for n in range(81)),
            'EGF_RECURRENCE', 'ordinary power coefficients do not match EGF integer recurrence')
    if terms_file is not None:
        require(parse_bfile(terms_file)==h, 'RECURRENCE_TERMS', 'delivered 501-term data differs from the regenerated recurrence')
    passed('501 exact integer terms; delivered 501-term fixture; 29 external OEIS display terms; independent EGF recurrence through n=80')
    if bfile:
        require(parse_bfile(bfile)==h,'OEIS_BFILE','OEIS b-file differs from recurrence')
        passed('501 externally retrieved OEIS b-file terms, indices 0..500')
    P=f['pole_coefficient']; L=f['factorial_coefficient']
    require(P>0 and P*3*4*5==P*P, 'POLE_COEFFICIENT', 'positive cubic pole fails y\'\'\'=y^2')
    require(P/2==L, 'FACTORIAL_COEFFICIENT', 'EGF pole transfer requires coefficient 30')
    require(all(P*comb(n+2,2)*factorial(n)==L*factorial(n+2) for n in range(30)),
            'FACTORIAL_TRANSFER','exact factorial/binomial identity fails')
    # Radical comparisons reduced to positive integer powers, no decimal rounding.
    require(180**3<=60**4 and 180**5<=720**4 and 720**3<=60**5,
            'RHO_COMPARISON','comparison-solution initial inequalities fail')
    passed('cubic pole 60, factorial coefficient 30, exact algebra behind 180^(1/4)<=rho<=60^(1/3)')
    X,Y,b,v=s.symbols('X Y b v', positive=True)
    flowx,flowy=map(sr,f['normalized_flow'])
    require(f['normalized_flow']==[F(4,3),F(5,3)],'NORMALIZED_FLOW','normalized derivative coefficients differ')
    A,B,Dv=map(sr,f['lyapunov_coefficients'])
    V=A*(X-1)**2+B*(Y-1-s.log(Y))
    Vdot=s.diff(V,X)*flowx*(Y-X**2)+s.diff(V,Y)*flowy*(1-X*Y)
    zero(Vdot-Dv*((Y-1)**2/Y+(X-1)**2*(X+1)), 'LYAPUNOV_IDENTITY','exact derivative identity fails')
    require(Dv<0,'LYAPUNOV_SIGN','strictly negative prefactor required')
    # Direct chain-rule check before normalization, using symbolic y,y',y''.
    y,p,r=s.symbols('y p r', positive=True)
    u=p/y**s.Rational(4,3); vv=r/y**s.Rational(5,3)
    ds_dx=y**s.Rational(1,3)
    def flow_derivative(expr): return (s.diff(expr,y)*p+s.diff(expr,p)*r+s.diff(expr,r)*y*y)/ds_dx
    zero(flow_derivative(u)-(vv-s.Rational(4,3)*u*u),'NORMALIZED_FLOW','u chain rule fails')
    zero(flow_derivative(vv)-(1-s.Rational(5,3)*u*vv),'NORMALIZED_FLOW','v chain rule fails')
    passed('normalized real flow and Lyapunov identity, symbolically exact')
    a=K(*f['alpha']); ab=a.conjugate()
    require(a.b>0 and a+ab==K(13) and a*ab==K(60), 'ALPHA_ROOT','alpha must be (13+i sqrt(71))/2')
    # Expand (d/dsigma+3)(d/dsigma+4)(d/dsigma+5)(1+w)=60(1+w)^2.
    lam=s.symbols('lambda')
    fp=s.Poly(s.expand((lam+3)*(lam+4)*(lam+5)-120),lam)
    fc=[F(int(c.p),int(c.q)) for c in fp.all_coeffs()]+[F(60)]
    require(f['fowler_coefficients']==fc,'FOWLER_ODE','Fowler coefficients must be 1,12,47,-60; RHS 60')
    require(all(poly_eval(list(reversed(f['fowler_coefficients'][:4])),z)==K(0) for z in [K(1),-a,-ab]),
            'FOWLER_EIGENVALUES','linear eigenvalues fail characteristic equation')
    coeff=f['D_coefficients_ascending']
    zero(sum(sr(c)*b**j for j,c in enumerate(coeff))-((3-b)*(4-b)*(5-b)-120),
         'INDICIAL_POLYNOMIAL','D(b) coefficients differ')
    zero((3-b)*(4-b)*(5-b)-120+(b+1)*(b*b-13*b+60),
         'INDICIAL_FACTORIZATION','D(b) factorization fails')
    matrix=[[K(1),K(1),K(1)],[-a,-ab,K(1)],[a*a,ab*ab,K(1)]]
    det=sum((matrix[0][i]*matrix[1][(i+1)%3]*matrix[2][(i+2)%3]
             -matrix[0][i]*matrix[1][(i+2)%3]*matrix[2][(i+1)%3] for i in range(3)),K())
    require(det==K(0,74), 'EIGENVECTOR_DETERMINANT','stable/unstable eigenvector determinant must be 74 i sqrt(71)')
    passed('Fowler ODE, three eigenvalues, indicial factorization, and nonzero eigenvector determinant')
    N=s.symbols('N',integer=True,positive=True)
    lower=(s.Rational(13,2)*N+1)*(s.Rational(13,2)*(N-1))**2
    require(sr(f['denominator_lower_bound'])==lower.subs(N,2),'DENOMINATOR_BOUND','wrong minimum denominator bound')
    x=s.symbols('x',nonnegative=True)
    require(all(c>=0 for c in s.Poly(s.expand(lower.subs(N,x+2)-lower.subs(N,2)),x).all_coeffs()),
            'DENOMINATOR_MONOTONICITY','nonnegative shifted polynomial certificate fails')
    M=f['catalan_M']
    require(M==60/f['denominator_lower_bound'],'CATALAN_CONSTANT','M must equal 60 divided by the denominator bound')
    # sqrt solution has its first discriminant zero at r=1/(8M).
    rr=s.symbols('r'); MM=sr(M)
    major=(1-s.sqrt(1-8*MM*rr))/(2*MM)
    zero(major-2*rr-MM*major**2,'CATALAN_IDENTITY','majorant does not solve A=2r+M A^2')
    coeffs={(1,0):K(1),(0,1):K(1)}
    degree=f['psi_degree']
    def dp(z): return poly_eval(coeff,z)
    for total in range(2,degree+1):
        for k in range(total+1):
            ell=total-k; beta=k*a+ell*ab
            bound=F((13*total+2)*169*(total-1)**2,8)
            require(dp(beta).norm2()>=bound**2,'DENOMINATOR_EXACT','degree-wise squared modulus bound fails')
            conv=sum((coeffs.get((p,q),K())*coeffs.get((k-p,ell-q),K())
                      for p in range(k+1) for q in range(ell+1)),K())
            coeffs[k,ell]=K(60)*conv/dp(beta)
    require(coeffs[2,0]==K(*f['a20']),'PSI_A20','a20 differs from exact recurrence')
    require(coeffs[1,1]==K(*f['a11']),'PSI_A11','a11 differs from exact recurrence')
    squared={}
    for (p,q),xval in coeffs.items():
        for (r,t),yval in coeffs.items():
            if p+q+r+t<=degree:
                squared[p+r,q+t]=squared.get((p+r,q+t),K())+xval*yval
    for (k,ell),val in coeffs.items():
        require(val.conjugate()==coeffs[ell,k],'PSI_CONJUGATION','quadratic-field conjugation fails')
        conv=sum((coeffs.get((p,q),K())*coeffs.get((k-p,ell-q),K())
                  for p in range(k+1) for q in range(ell+1)),K())
        require(dp(k*a+ell*ab)*val-60*squared.get((k,ell),K())==K(), 'PSI_PDE_RESIDUAL','nonzero retained PDE coefficient')
    # Finite Catalan coefficients are checked without floating-point moduli.
    cats=[F(0)]+[F(comb(2*n-2,n-1),n)*2**n*M**(n-1) for n in range(1,degree+1)]
    for n in range(2,degree+1):
        require(cats[n]==M*sum(cats[i]*cats[n-i] for i in range(1,n)),
                'CATALAN_RECURRENCE','Catalan formula fails checked recurrence')
    passed(f'nonresonance bound polynomial certificate; Catalan identity; exact psi recurrence/conjugation/PDE through total degree {degree}')
    # Exact generalized-binomial identity uses rising factorial (3-beta)_n/n!.
    # The gamma expression is the same product by Gamma(z+1)=z Gamma(z).
    beta=s.symbols('beta')
    for n in range(13):
        zero(s.Integer(-1)**n*s.prod(beta-3-j for j in range(n))/factorial(n)
             -s.prod(3-beta+j for j in range(n))/factorial(n),
             'BINOMIAL_TRANSFER','rising/falling factorial transfer identity fails')
    require(f['transfer_relative_multiplier']==2,'TRANSFER_MULTIPLIER','relative coefficient must equal 60/30=2')
    correction=sum(sr(c)*beta**j for j,c in enumerate(f['stirling_correction_ascending']))
    zero(correction-((3-beta)-3)*((3-beta)+3-1)/2,
         'STIRLING_CORRECTION','gamma-ratio correction must be beta(beta-5)/2')
    gamma_d=[s.Integer(1)]
    gamma_ell={r:s.expand(s.Rational((-1)**(r+1),r*(r+1))*(s.bernoulli(r+1,3-beta)-s.bernoulli(r+1,3))) for r in range(1,7)}
    for j in range(1,7):
        gamma_d.append(s.expand(sum(r*gamma_ell[r]*gamma_d[j-r] for r in range(1,j+1))/j))
    zero(gamma_d[1]-correction,'STIRLING_CORRECTION','Bernoulli log-ratio derivation disagrees')
    d2=sum(sr(c)*beta**j for j,c in enumerate(f['second_stirling_correction_ascending']))
    zero(gamma_d[2]-d2,'SECOND_STIRLING_CORRECTION','d2 must be b(b+1)(3b^2-29b+74)/24')
    # Exponentiating the finite log series independently checks the recurrence.
    tau=s.symbols('tau')
    for j in range(1,5):
        logpoly=sum(gamma_ell[r]*tau**r for r in range(1,j+1))
        coefficient=sum(s.expand(logpoly**m).coeff(tau,j)/s.factorial(m) for m in range(j+1))
        zero(gamma_d[j]-coefficient,'GAMMA_BERNOULLI_RECURRENCE','finite exp(log) coefficient disagrees')
    # beta=13k gives polynomial degree 13k-3; all later coefficients vanish.
    require(all(s.prod(3-13*k+j for j in range(13*k-2))==0 for k in range(1,6)),
            'DIAGONAL_POLYNOMIAL','integer-exponent polynomial cancellation fails')
    passed('gamma/product transfer, diagonal cancellation, d1 and d2, Bernoulli recurrence through order 6 and exp-log crosscheck through order 4')
    # Formal inverse: e=1/N0, delta=N-N0; a=(1/2)log(2pi N0), d=1+W.
    # The exact formal residual is d delta + a + sum_{m>=2}(-1)^m e^(m-1)
    # delta^m/[m(m-1)] + (1/2)log(1+e delta)
    # + sum_{k>=1} B_(2k)e^(2k-1)(1+e delta)^(-(2k-1))/[2k(2k-1)].
    e,aa,dd=s.symbols('epsilon a d', nonzero=True)
    inv_order=f['inverse_epsilon_order']
    def residual_coefficient(delta,order):
        # Truncated polynomial convolution: no terms above the requested degree
        # are constructed, so higher-order verification remains tractable.
        def power_coefficient(power, target):
            if target < 0: return s.Integer(0)
            arr=[s.Integer(1)]+[s.Integer(0)]*target
            for _ in range(power):
                arr=[s.expand(sum(arr[i]*delta[j-i] for i in range(j+1)
                                  if j-i<len(delta))) for j in range(target+1)]
            return arr[target]
        out=dd*(delta[order] if order<len(delta) else 0)+(aa if order==0 else 0)
        for m in range(2,order+2):
            out+=s.Rational((-1)**m,m*(m-1))*power_coefficient(m,order-m+1)
        for m in range(1,order+1):
            out+=s.Rational((-1)**(m+1),2*m)*power_coefficient(m,order-m)
        for k in range(1,(order+1)//2+1):
            pwr=2*k-1
            for j in range(order-pwr+1):
                out+=s.bernoulli(2*k)/s.Integer(2*k*(2*k-1))*((-1)**j*s.binomial(pwr+j-1,j))*power_coefficient(j,order-pwr-j)
        return s.cancel(out)
    ds=[-aa/dd]
    for j in range(1,inv_order+1):
        ds.append(s.cancel(-residual_coefficient(ds,j)/dd))
    x2,x1,x0=map(sr,f['lambert_second_correction'])
    zero(ds[1]+(x2*aa**2/dd**2+x1*aa/dd+x0)/dd,
         'LAMBERT_SECOND_CORRECTION','coefficient of 1/N0 differs')
    # Check each finite order separately to avoid needlessly expanding powers
    # of a full high-order polynomial beyond the coefficient being verified.
    for j in range(inv_order+1):
        zero(residual_coefficient(ds[:j+1],j),'INVERSE_RECURSION','nonzero formal epsilon residual')
    passed(f'Lambert first two corrections; formal epsilon inverse recurrence checked through epsilon^{inv_order}')
    return {'status':'PASS_EXACT_FINITE_CHECKS','checks':checks,'integer_term_count':len(h),
            'oeis_display_term_count':29,'oeis_bfile_term_count':501 if bfile else 0,
            'terms_sha256':hashlib.sha256(terms_text(h).encode()).hexdigest(),
            'psi_coefficients_Q_sqrt_minus_71':{f'{k},{ell}':val.record() for (k,ell),val in sorted(coeffs.items())},
            'inverse_delta_coefficients':[str(s.factor(t)) for t in ds],
            'limitations':['Finite checks do not prove analytic continuation, stable-surface completeness, singularity transfer hypotheses, or the asymptotic theorem.',
                           'No decimal estimate of rho or C is certified by this checker.',
                           'The all-degree denominator certificate is algebraic; its use in analytic convergence needs the argument in the report.']},h

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--fixture',type=Path,default=ROOT/'fixtures.json')
    ap.add_argument('--bfile',type=Path)
    ap.add_argument('--terms-file',type=Path,default=ROOT/'recurrence_terms_0_500.txt')
    ap.add_argument('--output',type=Path)
    ap.add_argument('--terms-output',type=Path)
    args=ap.parse_args()
    try:
        report,h=run(load_fixture(args.fixture),args.bfile,args.terms_file)
        out=json.dumps(report,indent=2)+'\n'
        if args.output: args.output.write_text(out)
        if args.terms_output: args.terms_output.write_text(terms_text(h))
        print(out,end='')
        return 0
    except VerificationError as exc:
        print(f'CHECK_FAILED {exc}',file=sys.stderr)
        return 2
if __name__=='__main__': sys.exit(main())
