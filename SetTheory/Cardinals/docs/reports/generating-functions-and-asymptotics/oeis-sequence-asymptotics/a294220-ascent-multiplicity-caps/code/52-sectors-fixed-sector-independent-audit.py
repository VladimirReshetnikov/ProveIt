#!/usr/bin/env python3
"""Independent checks: discrete-geometric expansion and exact rational Laplace integrals.
Uses no imported author code. Run from any directory; prints JSON. Requires sympy, mpmath.
"""
import hashlib, json, math
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import sympy as S
import mpmath as mp
BASE = Path(__file__).resolve().parent

def geometric_coefficients(r, n=3):
    # Expand the exact positive-tail Laplace sum in independent geometric indices.
    j = S.symbols('j0:'+str(r)); J = sum(j); i, h, z = S.symbols('i h z')
    q = S.Rational(r,r+1); H = S.harmonic(r)
    logcorr = [S.S.Zero]
    for k in range(1,n+1):
        p = S.summation(i**k,(i,1,z))
        logcorr.append(S.expand(S.Rational((-1)**(k+1),k)*(p.subs(z,J)/r**k-sum(p.subs(z,a) for a in j))))
    expcorr = [S.S.One]
    for k in range(1,n+1):
        expcorr.append(S.expand(sum(a*logcorr[a]*expcorr[k-a] for a in range(1,k+1))/k))
    linear = (J+1-(r+1)*H)/r
    polys = [expcorr[k] + (linear*expcorr[k-1] if k else 0) for k in range(n+1)]
    moments = {0:S.S.One}; t = 1/(1-z)
    for k in range(1,2*n+2):
        t = S.cancel(z*S.diff(t,z)); moments[k] = S.factor((1-q)*t.subs(z,q))
    def average(poly):
        return S.factor(sum(c*S.prod(moments[a] for a in powers) for powers,c in S.Poly(S.expand(poly),*j).terms()))
    expectation = sum(average(polys[k])*h**k for k in range(n+1))
    stirling = sum(S.bernoulli(2*k)*(S.Rational(r)**(1-2*k)-r)*h**(2*k-1)/(2*k*(2*k-1)) for k in range(1,(n+1)//2+1))
    in_m = S.series(expectation*S.exp(stirling),h,0,n+1).removeO().expand()
    in_b = S.series((1+h)**S.Rational(3-r,2)*in_m.subs(h,h/(1+h)),h,0,n+1).removeO().expand()
    return {'relative_m_coefficients':[str(S.factor(in_m.coeff(h,k))) for k in range(n+1)],'relative_b_coefficients':[str(S.factor(in_b.coeff(h,k))) for k in range(n+1)]}

@lru_cache(None)
def exact_J(r,b):
    # E_b(v)^k = sum_n d[k,n] v^n/n!. All d are exact integers.
    H=sum((F(1,j) for j in range(1,r+1)),F(0)); total=F(0); d=[1]
    for k in range(r+1):
        rate=k+1
        total += (-1)**k*math.comb(r,k)*sum((F(a,rate**(n+2))*(n+1-rate*H) for n,a in enumerate(d)),F(0))
        if k<r:
            nd=[0]*((k+1)*b+1)
            for n,a in enumerate(d):
                choose=1
                for j in range(b+1):
                    if j: choose=choose*(n+j)//j
                    nd[n+j]+=a*choose
            d=nd
    return total

def normalized_J(r,b):
    v=exact_J(r,b)
    C=mp.mpf(r)**(mp.mpf(r)+mp.mpf('1.5'))/(r+1)**2*(2*mp.pi)**(mp.mpf(1-r)/2)
    beta=(mp.mpf(r)/(r+1))**r
    return mp.mpf(v.numerator)/v.denominator/(C*mp.mpf(b)**(mp.mpf(3-r)/2)*beta**b)

def main():
    mp.mp.dps=90
    author=json.loads((BASE/'fixed-sector-validation.json').read_text())
    out={'source_sha256':{f:hashlib.sha256((BASE/f).read_bytes()).hexdigest() for f in ['fixed-taylor-sectors.md','fixed-sector-verify.py','fixed-sector-validation.json']}}
    out['independent_discrete_geometric_coefficients']={str(r):geometric_coefficients(r) for r in (1,2,3,4)}
    out['coefficient_match']=out['independent_discrete_geometric_coefficients']==author['coefficients']
    # Direct symbolic differentiation checks the exact a_r formula.
    x=S.symbols('x',positive=True); f=S.log(x)/(x-1)
    derivative=[]
    for r in range(1,7):
        expected=x**(-r-1)*(S.log(x)-sum((1-1/x)**j/S.Integer(j) for j in range(1,r+1)))/(1-1/x)**(r+1)
        derivative.append(S.simplify((-1)**r*S.diff(f,x,r)/S.factorial(r)-expected)==0)
    out['symbolic_derivative_identity_r1_to_r6']=derivative
    out['exact_J1_identity_b0_to_b30']=all(exact_J(1,b)==F(b+1,2**(b+2)) for b in range(31))
    out['exact_rational_laplace_checks']={}
    for r in (2,3):
        for b in (50,100,200):
            got=normalized_J(r,b); expected=mp.mpf(author['normalized_principal_sector'][str(r)][str(b)])
            out['exact_rational_laplace_checks'][f'r{r}_b{b}']={'normalized':mp.nstr(got,55),'absolute_error_from_author_45_digit_value':mp.nstr(abs(got-expected),8),'matches_to_44_decimal_places':abs(got-expected)<mp.mpf('1e-44')}
    out['exact_A1_zeta_checks']={}
    for b in (20,50,100):
        got=(mp.mpf(b+1)*(mp.zeta(b+2)-1))/(mp.mpf(b)/2**(b+2))
        expected=mp.mpf(author['normalized_exact_sector']['1'][str(b)])
        out['exact_A1_zeta_checks'][str(b)]={'normalized':mp.nstr(got,55),'absolute_error_from_author_45_digit_value':mp.nstr(abs(got-expected),8),'matches_to_44_decimal_places':abs(got-expected)<mp.mpf('1e-44')}
    out['all_checks_pass']=out['coefficient_match'] and all(derivative) and out['exact_J1_identity_b0_to_b30'] and all(v['matches_to_44_decimal_places'] for v in out['exact_rational_laplace_checks'].values()) and all(v['matches_to_44_decimal_places'] for v in out['exact_A1_zeta_checks'].values())
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
