#!/usr/bin/env python3
"""CM row-product certificates: exact arithmetic + directed interval q-series.

No integer-relation search is used.  The Hilbert polynomial proof combines
the classical integrality theorem with coefficient enclosures of width < 1.
The gamma-product comparisons at the end are numerical regression checks;
the analytic norm formula is proved in cm_norms.tex.
"""
from fractions import Fraction
from functools import reduce
from math import gcd, isqrt
from pathlib import Path
import json
import mpmath as mp
import sympy as sp

X = sp.Symbol('X')
H = {
    15: X**2 + 191025*X - 121287375,
    20: X**2 - 1264000*X - 681472000,
    23: X**3 + 3491750*X**2 - 5151296875*X + 12771880859375,
    39: X**4 + 331531596*X**3 - 429878960946*X**2
        + 109873509788637459*X + 20919104368024767633,
    47: X**5 + 2257834125*X**4 - 9987963828125*X**3
        + 5115161850595703125*X**2 - 14982472850828613281250*X
        + 16042929600623870849609375,
}

def reduced_forms(d):
    ans = []
    for a in range(1, isqrt(d//3) + 1):
        for b in range(-a, a+1):
            if (b*b+d) % (4*a):
                continue
            c = (b*b+d)//(4*a)
            if c < a or gcd(gcd(a, abs(b)), c) != 1:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            ans.append((a,b,c))
    return ans

def mpf_fraction(t):
    """Exact rational value of a finite internal binary mpf endpoint."""
    sign, man, exponent, _ = t
    return Fraction((-1 if sign else 1)*man) * Fraction(2)**exponent

def bounds(iv):
    return tuple(mpf_fraction(t) for t in iv._mpi_)

def iv_fraction(x):
    x = Fraction(x)
    return mp.iv.mpf(x.numerator)/x.denominator

def error_box(radius):
    err = mp.iv.mpf([-1,1])*iv_fraction(radius)
    return mp.iv.mpc(err,err)

def tail_bound(p,n):
    """Bound sum_{k>n} k^p q^k/(1-q^k), |q|<1/200.

    k=n+1+j <= (n+1)(j+1), and
    sum (j+1)^p r^j = Eulerian_p(r)/(1-r)^(p+1).
    """
    r = Fraction(1,200)
    euler = {3:(1,4,1),5:(1,26,66,26,1)}[p]
    numerator = sum(c*r**j for j,c in enumerate(euler))
    return (n+1)**p*r**(n+1)*numerator/(1-r)**(p+2)

def iv_eisenstein(d,form,n=70):
    a,b,c = form
    tau = mp.iv.mpc(-iv_fraction(Fraction(b,2*a)),mp.iv.sqrt(d)/(2*a))
    q = mp.iv.exp(mp.iv.mpc(0,2)*mp.iv.pi*tau)
    s3 = mp.iv.mpc(0); s5 = mp.iv.mpc(0)
    qn = q
    for k in range(1,n+1):
        term = qn/(1-qn)
        s3 += k**3*term
        s5 += k**5*term
        qn *= q
    e4 = 1+240*s3+error_box(240*tail_bound(3,n))
    e6 = 1-504*s5+error_box(504*tail_bound(5,n))
    delta = (e4**3-e6**2)/1728
    return e4,e6,delta,e4**3/delta

def polynomial_certificate(d,n=70):
    """Certify every coefficient as an integer by intervals and CM integrality."""
    forms = reduced_forms(d)
    coeff = [mp.iv.mpc(1)]
    for form in forms:
        j = iv_eisenstein(d,form,n)[3]
        nxt = [mp.iv.mpc(0) for _ in range(len(coeff)+1)]
        for k,c in enumerate(coeff):
            nxt[k] -= j*c
            nxt[k+1] += c
        coeff = nxt
    expected = list(reversed(sp.Poly(H[d],X).all_coeffs()))
    assert len(coeff) == len(expected)
    result = []
    for k,(actual,integer) in enumerate(zip(coeff,expected)):
        integer = int(integer)
        re_lo,re_hi = bounds(actual.real)
        im_lo,im_hi = bounds(actual.imag)
        assert re_lo <= integer <= re_hi, (d,k,'real exclusion')
        assert im_lo <= 0 <= im_hi, (d,k,'imaginary exclusion')
        assert integer-Fraction(1,2) < re_lo <= re_hi < integer+Fraction(1,2)
        result.append({
            'degree':k,'coefficient':str(integer),
            'real_error_lower':str(re_lo-integer),
            'real_error_upper':str(re_hi-integer),
            'imaginary_lower':str(im_lo),'imaginary_upper':str(im_hi),
            'real_interval_width':str(re_hi-re_lo),
        })
    return {'discriminant':-d,'forms':forms,'terms':n,
            'interval_dps':mp.iv.dps,'coefficients':result,
            'maximum_real_width':str(max(bounds(c.real)[1]-bounds(c.real)[0] for c in coeff)),
            'certified_by_integrality':True}

def eis(w,tau,n=120):
    q=mp.exp(2j*mp.pi*tau)
    qn=q; total=mp.mpc(0)
    for k in range(1,n+1):
        total+=k**(w-1)*qn/(1-qn)
        qn*=q
    return 1-2*w/mp.bernoulli(w)*total

def gamma_p(d):
    return mp.fprod(mp.gamma(mp.mpf(r)/d) for r in range(1,d)
                    if sp.kronecker_symbol(-d,r)==1)

def norm_formula(d,w):
    forms=reduced_forms(d); h=len(forms)
    aprod=sp.prod(a for a,b,c in forms)
    phi=sp.totient(d)
    cyclo=sp.cyclotomic_poly(d,X).subs(X,1)
    f={4:X**4,6:(X-1728)**6,8:X**8,10:X**4*(X-1728)**6,
       12:(X-sp.Rational(432000,691))**12}[w]
    res=abs(sp.resultant(H[d],f,X))
    r=mp.mpf(str(res.p))/int(res.q) if hasattr(res,'q') else mp.mpf(str(res))
    return ((abs(mp.bernoulli(w))/mp.factorial(w))**h
            * (mp.mpf(int(aprod))/mp.mpf(d)**h)**(mp.mpf(w)/2)
            * mp.mpf(int(cyclo))**(mp.mpf(w)/4)
            * (2*mp.pi)**(mp.mpf(w)*(2*h-int(phi))/4)
            * gamma_p(d)**w * r**(mp.mpf(1)/12))

def regression(d,w):
    forms=reduced_forms(d)
    lhs=mp.fprod(2*mp.zeta(w)*eis(w,mp.mpc(-mp.mpf(b)/(2*a),mp.sqrt(d)/(2*a)))
                 for a,b,c in forms)
    rhs=norm_formula(d,w)
    return {'discriminant':-d,'weight':w,'absolute_product':mp.nstr(abs(lhs),30),
            'formula':mp.nstr(rhs,30),'relative_residual':mp.nstr(abs(abs(lhs)-rhs)/rhs,8),
            'product_phase':mp.nstr(mp.arg(lhs),15),'numeric_dps':mp.mp.dps}

def explicit_checks():
    p23=gamma_p(23);p39=gamma_p(39);p47=gamma_p(47)
    rhs={
      23:mp.mpf(11)**2*19*p23**6/(mp.mpf(2)**33*3**9*5**3*23**7*mp.pi**24),
      39:mp.mpf(19)**2*23*p39**6/(mp.mpf(2)**38*3**15*5**4*13**12*mp.pi**24),
      47:mp.mpf(11)**3*19**2*23**2*31*43*p47**6/(mp.mpf(2)**73*3**9*5**5*7**5*47**13*mp.pi**54),
    }
    return {str(-d):mp.nstr(abs(norm_formula(d,6)-v)/v,8) for d,v in rhs.items()}

def main():
    mp.iv.dps=120
    mp.mp.dps=120
    # A rational proof of the common q bound used above:
    assert sum(Fraction(27,5)**k/sp.factorial(k) for k in range(16)) > 200
    assert Fraction(314,100)*Fraction(173,100) > Fraction(27,5)
    cert=[polynomial_certificate(d) for d in H]
    vals=[regression(d,w) for d in H for w in (4,6,8,10,12)]
    factors={str(-d):{
       'H_at_zero_factorization':{str(p):int(e) for p,e in sp.factorint(H[d].subs(X,0)).items()},
       'H_at_1728_factorization':{str(p):int(e) for p,e in sp.factorint(H[d].subs(X,1728)).items()},
       'leading_coefficient_product':int(sp.prod(a for a,b,c in reduced_forms(d))),
       'H_at_432000_over_691':str(H[d].subs(X,sp.Rational(432000,691))),
    } for d in H}
    receipt={'engine':{'mpmath':mp.__version__,'sympy':sp.__version__},
             'proof_method':'CM integrality plus outward interval Lambert-series coefficient enclosures',
             'class_polynomial_certificates':cert,'exact_factorizations':factors,
             'numerical_regressions':vals,'explicit_weight_six_checks':explicit_checks()}
    dest=Path(__file__).with_name('cm_norms_receipt.json')
    dest.write_text(json.dumps(receipt,indent=2)+'\n')
    for c in cert:
        width=Fraction(c['maximum_real_width'])
        print('H',c['discriminant'],'certified;',len(c['coefficients']),'coefficients;',
              'maximum width',mp.nstr(mp.mpf(width.numerator)/width.denominator,6))
    for v in vals:print('gamma norm',v['discriminant'],v['weight'],v['relative_residual'])
    print('explicit weight-six checks',receipt['explicit_weight_six_checks'])
    print('receipt',dest)

if __name__=='__main__':main()
