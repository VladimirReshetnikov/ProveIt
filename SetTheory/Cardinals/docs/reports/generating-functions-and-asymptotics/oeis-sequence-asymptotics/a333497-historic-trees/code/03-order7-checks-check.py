#!/usr/bin/env python3
"""Exact, finite reader checks. This program does not certify analytic proofs."""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import comb, factorial
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent

class CheckFailure(Exception):
    def __init__(self, name, detail):
        self.name, self.detail = name, detail
        super().__init__(f'{name}: {detail}')

def need(condition, name, detail):
    # Deliberately not an assert: every guard remains active under python -O.
    if not condition:
        raise CheckFailure(name, detail)

def exact_json(path, name):
    def unique(pairs):
        d = {}
        for k, v in pairs:
            need(k not in d, name, f'duplicate JSON key: {k}')
            d[k] = v
        return d
    try:
        return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique,
                          parse_constant=lambda x: (_ for _ in ()).throw(CheckFailure(name, f'nonfinite JSON token {x}')))
    except CheckFailure:
        raise
    except (OSError, ValueError, UnicodeError) as e:
        raise CheckFailure(name, str(e)) from None

def fraction(value, name):
    need(type(value) is str and re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?', value) is not None,
         name, f'not a strict rational string: {value!r}')
    return F(value)

def manifest_check(root):
    obj = exact_json(root/'MANIFEST.json', 'INTEGRITY_MANIFEST')
    need(type(obj) is dict and set(obj) == {'format', 'files'} and type(obj['format']) is int and obj['format'] == 1,
         'INTEGRITY_MANIFEST', 'expected format 1 and files mapping')
    files = obj['files']
    need(type(files) is dict and bool(files), 'INTEGRITY_MANIFEST', 'empty or invalid files map')
    for rel, expected in files.items():
        need(type(rel) is str and '\\' not in rel and not rel.startswith('/') and '..' not in Path(rel).parts
             and rel != 'MANIFEST.json' and Path(rel).as_posix() == rel, 'INTEGRITY_MANIFEST', f'unsafe entry {rel!r}')
        need(type(expected) is str and re.fullmatch('[0-9a-f]{64}', expected) is not None,
             'INTEGRITY_MANIFEST', f'invalid digest for {rel}')
        p = root/rel
        need(p.is_file() and not p.is_symlink(), 'INTEGRITY_MISSING', rel)
        need(sha256(p.read_bytes()).hexdigest() == expected, 'INTEGRITY_HASH', rel)
    actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()
              and '__pycache__' not in p.parts and p.relative_to(root).as_posix() != 'MANIFEST.json'}
    need(actual == set(files), 'INTEGRITY_UNLISTED', ', '.join(sorted(actual-set(files))))
    return len(files)

class Q:
    """Exact Q(sqrt(-159)); coefficients are fractions, never floating point."""
    __slots__ = ('r', 'i')
    def __init__(self, r=0, i=0): self.r, self.i = F(r), F(i)
    @staticmethod
    def of(a): return a if isinstance(a, Q) else Q(a)
    def __add__(self, other):
        b=Q.of(other); return Q(self.r+b.r, self.i+b.i)
    __radd__=__add__
    def __neg__(self): return Q(-self.r,-self.i)
    def __sub__(self,b): return self+-Q.of(b)
    def __rsub__(self,b): return Q.of(b)+-self
    def __mul__(self,other):
        b=Q.of(other); return Q(self.r*b.r-159*self.i*b.i, self.r*b.i+self.i*b.r)
    __rmul__=__mul__
    def __truediv__(self, other):
        b=Q.of(other); den=b.r*b.r+159*b.i*b.i
        need(den != 0, 'NONRESONANCE_DENOMINATOR', 'division by zero in quadratic field')
        return self*Q(b.r/den,-b.i/den)
    def __rtruediv__(self,b): return Q.of(b)/self
    def __pow__(self,n):
        need(type(n) is int and n >= 0, 'QUADRATIC_POWER', str(n))
        ans=Q(1)
        for _ in range(n): ans=ans*self
        return ans
    def __eq__(self,b):
        b=Q.of(b); return self.r == b.r and self.i == b.i
    def conj(self): return Q(self.r,-self.i)
    def pair(self): return [str(self.r), str(self.i)]

ALPHA=Q(F(11,2),F(1,2))
def beta(nu): return 12*nu[0]+ALPHA*nu[1]+ALPHA.conj()*nu[2]
def indicial(b): return (b+1)*(b-12)*(b*b-11*b+70)
def indices(n):
    return [(k,l,n-k-l) for k in range(n+1) for l in range(n-k+1)]
def subindices(nu):
    k,l,m=nu
    return [(p,q,u) for p in range(k+1) for q in range(l+1) for u in range(m+1)]
def series_coefficients(degree):
    a={(0,0,0):Q(0), (1,0,0):Q(1), (0,1,0):Q(1), (0,0,1):Q(1)}
    for n in range(2,degree+1):
        for nu in indices(n):
            conv=sum((a.get(mu,Q())*a.get(tuple(x-y for x,y in zip(nu,mu)),Q()) for mu in subindices(nu)),Q())
            a[nu]=840*conv/indicial(beta(nu))
    return a

def read_terms(path):
    try: lines=path.read_text(encoding='ascii').splitlines()
    except (OSError,UnicodeError) as e: raise CheckFailure('TERMS_FORMAT',str(e)) from None
    need(len(lines)==501, 'TERMS_COUNT', f'expected 501 rows; got {len(lines)}')
    result=[]
    for n,line in enumerate(lines):
        need(re.fullmatch(r'(?:0|[1-9][0-9]*) [1-9][0-9]*',line) is not None,
             'TERMS_FORMAT', f'malformed row {n}')
        idx,val=map(int,line.split())
        need(idx==n, 'TERMS_INDEX', f'row {n} has index {idx}')
        result.append(val)
    return result

def recurrence_checks(root):
    fixture=read_terms(root/'fixtures/recurrence_terms_0_500.txt')
    h=[1]*4
    for n in range(497):
        h.append(sum(comb(n,k)*h[k]*h[n-k] for k in range(n+1)))
    # Independent arithmetic representation: ordinary Taylor coefficients of H,
    # square the rational series and integrate four times; no binomials used.
    ordinary=[F(1,factorial(j)) for j in range(4)]
    for n in range(497):
        convolution=sum((ordinary[k]*ordinary[n-k] for k in range(n+1)),F())
        ordinary.append(convolution/((n+1)*(n+2)*(n+3)*(n+4)))
    recovered=[x*factorial(n) for n,x in enumerate(ordinary)]
    need(all(x.denominator==1 for x in recovered), 'TERMS_INTEGRAL', 'EGF computation was not integral')
    need(h==recovered, 'TERMS_TWO_METHODS', 'binomial recurrence and rational EGF integration differ')
    need(h==fixture, 'TERMS_METHODS_FIXTURE', 'generated terms differ from frozen fixture')
    oeis=exact_json(root/'fixtures/oeis_A336009_prefix.json','OEIS_PREFIX_JSON')
    need(type(oeis) is dict and set(oeis)=={'sequence','source_url','verified_on','offset','terms','scope'},
         'OEIS_PREFIX_SCHEMA', 'unexpected OEIS prefix fields')
    need(oeis['sequence']=='A336009' and oeis['source_url']=='https://oeis.org/A336009' and oeis['offset']==0
         and type(oeis['offset']) is int and oeis['verified_on']=='2026-10-02',
         'OEIS_PREFIX_SCHEMA', 'incorrect provenance or offset')
    need(oeis['scope']=='Only these 31 displayed terms are externally checked; terms 31 through 500 are generated, not an external OEIS table.', 'OEIS_PREFIX_SCHEMA', 'scope disclosure differs')
    prefix=oeis['terms']
    need(type(prefix) is list and len(prefix)==31 and all(type(x) is int and x>0 for x in prefix),
         'OEIS_PREFIX_SCHEMA', 'expected 31 positive integers')
    need(prefix==h[:31], 'OEIS_PREFIX_REFERENCE', 'external displayed prefix differs from recurrence')
    return {'terms':501,'external_OEIS_display_terms':31,'independent_arithmetic_methods':2,
            'term_fixture_sha256':sha256((root/'fixtures/recurrence_terms_0_500.txt').read_bytes()).hexdigest()}

def symbolic_checks(root):
    try: import sympy as s
    except ImportError: raise CheckFailure('DEPENDENCY_SYMPY','install requirements.txt') from None
    ref=exact_json(root/'fixtures/reference_formulas.json','FORMULA_JSON')
    keys={'pole','egf','energy_coefficient','c0','catalan_M','real_M','D24','rmax','ratio_bound','stable_determinant_w','inverse_shift','inverse_scale','psi_degree2'}
    need(type(ref) is dict and set(ref)==keys,'FORMULA_SCHEMA','unexpected reference formula fields')
    val={k:fraction(v,'FORMULA_RATIONAL') for k,v in ref.items() if k!='psi_degree2'}
    b,d,t,u=s.symbols('b d t u',real=True)
    D=s.prod(j-b for j in range(4,8))-1680
    need(s.expand(D-(b+1)*(b-12)*(b*b-11*b+70))==0,'INDICIAL_FACTORIZATION','D factorization')
    need(s.expand(s.prod(d+j for j in range(4,8))-1680-(d**4+22*d**3+179*d*d+638*d-840))==0,
         'FOWLER_ODE','normalized polynomial')
    pole=val['pole']; egf=val['egf']
    need(pole>0 and pole*4*5*6*7==pole*pole,'CONSTANT_POLE_BALANCE','pole amplitude must solve A*840=A^2')
    need(egf==pole/factorial(3)==F(factorial(7),factorial(3)**2),'CONSTANT_EGF','EGF transfer factor')
    need(5**6<16800<6**6 and 840>4**4 and 840>20**2 and 840**3>120**4,
         'COMPARISON_CERTIFICATES','exact comparison inequalities')
    need(840**3>=16800**2,'COMPARISON_ORDER','R_- <= R_+')
    H=s.Function('H')(t); Fexpr=t**4*H/840
    for target in [(t**5*(-s.diff(H,t))-4*t**4*H)/840,
                   (t**6*s.diff(H,t,2)+9*t**5*s.diff(H,t)+16*t**4*H)/840,
                   (-t**7*s.diff(H,t,3)-15*t**6*s.diff(H,t,2)-61*t**5*s.diff(H,t)-64*t**4*H)/840]:
        Fexpr=-t*s.diff(Fexpr,t)
        need(s.expand(Fexpr-target)==0,'NORMALIZED_DERIVATIVES','sigma derivatives of t^4 H/840')
    w=s.sqrt(-159); alpha=(11+w)/2; abar=(11-w)/2
    mat=s.Matrix([[0,1,0,0],[0,0,1,0],[0,0,0,1],[840,-638,-179,-22]])
    columns=[s.Matrix([1,-r,r*r,-r**3]) for r in [12,alpha,abar]]+[s.ones(4,1)]
    for col,ev in zip(columns,[-12,-alpha,-abar,1]):
        need(all(s.simplify(x)==0 for x in mat*col-ev*col),'STABLE_EIGENVECTORS','matrix/eigenvector identity')
    det=s.expand_complex(s.Matrix.hstack(*columns).det())
    need(s.simplify(det-val['stable_determinant_w']*w)==0 and val['stable_determinant_w']!=0,
         'STABLE_DETERMINANT','invertible chart determinant')
    # This finite certificate verifies the polynomial inequality for all u>=0:
    # N=2+u; all coefficients in bound(N)-bound(2) are nonnegative.
    N=2+u; lower=(11*N/2+1)*s.Rational(1,2)*(11*(N-1)/2)**2
    coeffs=s.Poly(s.expand(lower-s.Rational(363,2)),u).all_coeffs()
    need(all(c>=0 for c in coeffs) and s.simplify(lower.subs(u,0))==s.Rational(363,2),
         'NONRESONANCE_BOUND','nonnegative polynomial certificate')
    solutions=[(k,j) for k in range(2) for j in range(3) if 24*k+11*j==24]
    need(solutions==[(1,0)],'NONRESONANCE_DIOPHANTINE','only degree-one real resonance')
    need(val['catalan_M']==F(840)/F(363,2)==F(560,121),'CATALAN_CONSTANT','840/(363/2)')
    x=s.symbols('x'); f=s.Function('f')(x)
    energy=s.diff(f,x,3)*s.diff(f,x)-s.diff(f,x,2)**2/2-f**3/3
    need(s.expand(s.diff(energy,x)-s.diff(f,x)*(s.diff(f,x,4)-f*f))==0,'ENERGY_IDENTITY','first-integral differentiation')
    a=s.symbols('a'); y=840*t**-4*(1+a*t**12)
    dz=lambda expr,n:(-1)**n*s.diff(expr,t,n)
    test=s.expand(dz(y,3)*dz(y,1)-dz(y,2)**2/2-y**3/3)
    need(s.expand(test.coeff(t,0)-s.Rational(val['energy_coefficient'].numerator,val['energy_coefficient'].denominator)*a)==0,
         'ENERGY_COEFFICIENT','constant energy coefficient')
    need(val['energy_coefficient']*val['c0']==F(1,6),'ENERGY_AMPLITUDE','exact c0')
    need(val['D24']==D.subs(b,24)==114600 and val['real_M']==840/val['D24']==F(7,955),
         'REAL_MODE_CONSTANTS','D(24) and scalar majorant')
    for factor in [b+1,b-12,b*b-11*b+70]:
        need(all(c>0 for c in s.Poly(s.expand(factor.subs(b,24+u)),u).all_coeffs()),
             'REAL_MODE_MONOTONICITY','positive shifted factor polynomial')
    need(val['rmax']==abs(val['c0'])*840**3==F(35,1066) and val['rmax']<F(1,30),
         'REAL_MODE_RADIUS','|c0| rho^12 rational bound')
    M=val['real_M']; r=F(1,30)
    need(1-4*M*r>F(14,15)**2 and 2*r/(1+F(14,15))==F(1,29) and F(15,14)<2,
         'REAL_MODE_MAJORANT','B<1/29 and Bprime<2 rational certificates')
    ratio=(4+12*r*2/(1-F(1,29)))/5
    need(val['ratio_bound']==ratio==F(169,175) and ratio<1,'REAL_MODE_RATIO','contradictory initial derivative ratio')
    degree=5; psi=series_coefficients(degree)
    psi_ref=ref['psi_degree2']
    need(type(psi_ref) is dict and set(psi_ref)=={'2,0,0','0,2,0','0,1,1'},'PSI_SCHEMA','degree-two fixture fields')
    for key,pair in psi_ref.items():
        need(type(pair) is list and len(pair)==2,'PSI_SCHEMA',key)
        expected=Q(fraction(pair[0],'PSI_RATIONAL'),fraction(pair[1],'PSI_RATIONAL'))
        need(psi[tuple(map(int,key.split(',')))]==expected,'PSI_COEFFICIENTS',key)
    for nu,c in psi.items():
        need(c.conj()==psi[(nu[0],nu[2],nu[1])],'PSI_CONJUGATION',str(nu))
        conv=sum((psi.get(mu,Q())*psi.get(tuple(x-y for x,y in zip(nu,mu)),Q()) for mu in subindices(nu)),Q())
        bn=beta(nu)
        qprod=Q(1)
        for j in range(4,8): qprod=qprod*(j-bn)
        need((qprod-1680)*c==840*conv,'PSI_PDE',str(nu))
    # One-variable Catalan coefficient domination through degree ten.
    real=[F(0),F(1)]; major=[F(0),F(1)]
    for k in range(2,11):
        real.append(F(840,int(D.subs(b,12*k)))*sum(real[j]*real[k-j] for j in range(1,k)))
        major.append(M*sum(major[j]*major[k-j] for j in range(1,k)))
        need(0<real[k]<=major[k]==F(comb(2*k-2,k-1),k)*M**(k-1),'REAL_MODE_CATALAN_COEFFICIENTS',str(k))
    transfer_checks(s,b,psi,val)
    gamma=gamma_checks(s,b)
    lambert=lambert_checks(s,val)
    monodromy=monodromy_algebra_checks(s,psi)
    return {'sympy_version':s.__version__, 'psi_total_degree':degree,'psi_monomials_including_zero':len(psi),
            'gamma_inverse_powers':gamma,'Lambert_inverse_powers':lambert,
            'monodromy_algebra':monodromy,
            'stable_chart_determinant':'87412 sqrt(-159)',
            'nonvanishing_rational_certificate':'169/175 < 1',
            'scope':'Finite algebraic checks; analytic continuation, convergence, transfer hypotheses and C != 0 require the report proofs.'}

def transfer_checks(s,b,psi,val):
    # Binomial theorem coefficient identity with arbitrary exponent, at finite n.
    for n in range(13):
        numerator=s.prod(4-b+j for j in range(n))
        relative=s.factor(numerator/s.factorial(n)/s.binomial(n+3,3))
        need(s.simplify(relative-6*numerator/s.factorial(n+3))==0,'TRANSFER_FACTOR','factor 6')
    for nu in psi:
        if sum(nu)>0 and nu[1]==nu[2]:
            exponent=12*nu[0]+11*nu[1]-4
            need(exponent>=7 and s.binomial(exponent,exponent+1)==0,'INTEGER_SECTOR_POLYNOMIAL',str(nu))
    need(F(11,2)*3==F(33,2) and 12+F(11,2)>F(33,2),'TRANSFER_CUTOFF','second-harmonic error cutoff')
    need(val['inverse_shift']==3 and val['inverse_scale']==val['egf']==140,
         'INVERSE_SCALE_SHIFT','N=x+3 and L=log(X rho/140)')
    # M0(N-3)=140 Gamma(N+1) rho^(-N-1): moving rho gives X*rho/140.
    N=s.symbols('N')
    need(s.expand((N-val['inverse_shift'])+4-(N+1))==0,'INVERSE_SCALE_SHIFT','gamma and rho exponent shift')

def gamma_checks(s,b):
    x=s.symbols('x'); K=4
    logs={j:s.expand((-1)**(j+1)*(s.bernoulli(j+1,4-b)-s.bernoulli(j+1,4))/(j*(j+1))) for j in range(1,K+1)}
    ds={0:s.Integer(1)}
    for k in range(1,K+1): ds[k]=s.factor(sum(j*logs[j]*ds[k-j] for j in range(1,k+1))/k)
    need(s.expand(ds[1]-b*(b-7)/2)==0,'GAMMA_FIRST_CORRECTION','b(b-7)/2')
    S=sum(ds[k]*x**k for k in range(K+1))
    expform=s.series(s.exp(sum(logs[k]*x**k for k in range(1,K+1))),x,0,K+1).removeO()
    need(s.expand(S-expform)==0,'GAMMA_BERNOULLI_RECURSION','exponential coefficients')
    lhs=s.series((1+x)**(-b)*sum(ds[k]*(x/(1+x))**k for k in range(K+1)),x,0,K+2).removeO()
    rhs=s.series((1+(4-b)*x)/(1+4*x)*S,x,0,K+2).removeO()
    need(s.expand(lhs-rhs)==0,'GAMMA_SHIFT_RECURRENCE','Gamma ratio n -> n+1 exact difference equation')
    return K

def lambert_checks(s,val):
    e,a,d,z=s.symbols('e a d z',nonzero=True)
    K=3
    W,rho,N=s.symbols('W rho N',positive=True)
    N0=s.E*rho*s.exp(W); L=s.E*rho*W*s.exp(W)
    leading=N*s.log(N/(s.E*rho))
    need(s.simplify(leading.subs(N,N0)-L)==0 and
         s.simplify(s.diff(leading,N).subs(N,N0)-(1+W))==0,
         'LAMBERT_START_IDENTITY','N0=L/W, W exp(W)=L/(e rho), derivative=1+W')
    def residual(displacement):
        ans=d*displacement+a
        ans+=sum((-1)**k*e**(k-1)*displacement**k/s.Integer(k*(k-1)) for k in range(2,K+3))
        ans+=sum((-1)**(k+1)*(e*displacement)**k/s.Integer(2*k) for k in range(1,K+2))
        for r in range(1,(K+2)//2+1):
            ans+=s.bernoulli(2*r)*e**(2*r-1)/s.Integer(2*r*(2*r-1))*(1+e*displacement)**(-(2*r-1))
        return s.series(ans,e,0,K+1).removeO().expand()
    ps=[-a/d]
    for j in range(1,K+1):
        old=sum(ps[k]*e**k for k in range(j))
        ps.append(s.factor(-residual(old).coeff(e,j)/d))
    expected=-((a*a/(2*d*d))-a/(2*d)+s.Rational(1,12))/d
    need(s.simplify(ps[1]-expected)==0,'LAMBERT_SECOND_CORRECTION','coefficient of 1/N0')
    need(s.expand(residual(sum(ps[k]*e**k for k in range(K+1))))==0,'LAMBERT_FORMAL_RECURSION','residual through fixed order')
    # Independently expand the leading Stirling function in epsilon and shift z.
    # At N0, log(N0/(e*rho))=d-1. The constant L cancels.
    core=((1/e+z)*((d-1)+s.log(1+e*z))-(d-1)/e)
    expanded=s.series(core,e,0,K+1).removeO().expand()
    target=d*z+sum((-1)**k*e**(k-1)*z**k/s.Integer(k*(k-1)) for k in range(2,K+2))
    need(s.expand(expanded-target)==0,'LAMBERT_TAYLOR_SIGNS','leading Stirling Taylor coefficients')
    return K

def monodromy_algebra_checks(s,psi):
    # These are finite algebra checks used by the corollary, not an infinite
    # branch-independence test. The report proves the analytic implication.
    a,b,c,k=s.symbols('a b c k',real=True)
    alpha=(11+s.sqrt(-159))/2; abar=(11-s.sqrt(-159))/2
    need(s.expand((12*a+b*alpha+c*abar-k*alpha).subs(b,k+c)-(12*a+11*c))==0,
         'PURE_EXPONENT_UNIQUENESS_ORDER7','remaining real part 12a+11c')
    alpha2=(13+s.sqrt(-71))/2; abar2=(13-s.sqrt(-71))/2
    need(s.expand((a*alpha2+b*abar2-k*alpha2).subs(a,k+b)-13*b)==0,
         'PURE_EXPONENT_UNIQUENESS_ORDER5','remaining real part 13b')
    need(12*11==12*(ALPHA+ALPHA.conj()),'GROUPED_EXPONENT_COLLISION','real and diagonal exponents can coincide')
    for n in range(2,6):
        conv=sum((psi[(0,j,0)]*psi[(0,n-j,0)] for j in range(1,n)),Q())
        need(indicial(n*ALPHA)*psi[(0,n,0)]==840*conv,'PURE_AXIS_RECURRENCE_ORDER7',str(n))
    z=s.symbols('z'); D2=lambda x:s.prod(j-x for j in range(3,6))-120
    v={1:s.Integer(1)}
    for n in range(2,4):
        divisor=s.expand(D2(n*alpha2))
        need(divisor!=0,'PURE_AXIS_DENOMINATOR_ORDER5',str(n))
        v[n]=s.simplify(s.expand_complex(60*sum(v[j]*v[n-j] for j in range(1,n))/divisor))
    need(s.simplify(v[2]-(359+57*s.sqrt(-71))/17978)==0,
         'PURE_AXIS_COEFFICIENT_ORDER5','displayed second pure coefficient')
    V=sum(v[n]*z**n for n in v)
    pde=s.expand(sum(D2(n*alpha2)*v[n]*z**n for n in v)-60*V*V)
    need(all(s.simplify(pde.coeff(z,n))==0 for n in range(1,4)),
         'PURE_AXIS_PDE_ORDER5','residual through degree three')
    for order,kap,ar in [(3,60,alpha2),(4,840,alpha)]:
        for degree in range(1,5):
            symbols=s.symbols(f'v1:{degree+1}')
            polynomial=sum(symbols[j-1]*z**j for j in range(1,degree+1))
            lhs=sum((s.prod(h-j*ar for h in range(order,2*order))-2*kap)*symbols[j-1]*z**j
                    for j in range(1,degree+1))
            need(s.expand(lhs).coeff(z,2*degree)==0 and
                 s.expand(kap*polynomial**2).coeff(z,2*degree)==kap*symbols[-1]**2,
                 'NONPOLYNOMIAL_DEGREE_OBSTRUCTION',f'order={order}, degree={degree}')
    # Verify the coefficient/operator conversion on a generic finite polynomial.
    n,theta=s.symbols('n theta'); shift=3
    f=s.symbols('f0:12'); polynomial=sum(f[m]*z**m for m in range(12))
    operator_value=0; qs=[]
    for j in range(shift+1):
        p=(j+1)*n*n+(2-j)*n+1
        q=s.expand(p*s.prod(n+h for h in range(1,j+1)));qs.append(q)
        op=s.Poly(q.subs(n,theta-j),theta)
        applied=0
        for (power,),coefficient in op.terms():
            term=polynomial
            for _ in range(power):term=z*s.diff(term,z)
            applied+=coefficient*term
        operator_value+=z**(shift-j)*applied
    operator_value=s.expand(operator_value)
    for row in range(8):
        expected=sum(qs[j].subs(n,row)*f[row+j] for j in range(shift+1))
        need(s.expand(operator_value.coeff(z,row+shift)-expected)==0,
             'P_RECURSIVE_EGF_OPERATOR',str(row))
    return {'order7_pure_degree':5,'order5_pure_degree':3,
            'scope':'Finite algebra only. Infinite nonzero support, branch independence and non-D-finiteness are proved in the report.'}

def run(root,check_integrity=True):
    files=manifest_check(root) if check_integrity else None
    recurrence=recurrence_checks(root)
    symbolic=symbolic_checks(root)
    return {'status':'PASS','kind':'EXACT_FINITE_CHECKS','manifest_files':files,
            'recurrence':recurrence,'symbolic':symbolic,
            'does_not_certify':['analytic proof hypotheses','decimal digits of rho or C','infinite monodromy','literature novelty']}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=ROOT)
    parser.add_argument('--skip-integrity',action='store_true',help='for development/mutation diagnostics only; not a sealed-bundle PASS')
    args=parser.parse_args()
    try: result=run(args.root.resolve(),not args.skip_integrity)
    except CheckFailure as e:
        print(json.dumps({'status':'FAIL','diagnostic':e.name,'detail':e.detail},indent=2)); return 1
    except Exception as e:
        # Unexpected exceptions are never mistaken for an expected diagnostic.
        print(json.dumps({'status':'ERROR','diagnostic':'UNEXPECTED_EXCEPTION','detail':f'{type(e).__name__}: {e}'},indent=2)); return 2
    print(json.dumps(result,indent=2,sort_keys=True)); return 0
if __name__=='__main__': sys.exit(main())
