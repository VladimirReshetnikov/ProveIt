#!/usr/bin/env python3
"""Certify the three CM genus ratios proved in cm_genus.tex.

Exact symbolic arithmetic proves the factorizations and cubic identities.
Directed intervals identify each CM root's genus factor, using the already
certified integral Hilbert polynomial. Decimal row evaluations at the end
are independent numerical regressions, not the proof of the identities.
Run alongside cm_norms.py; requires mpmath and sympy.
"""
from fractions import Fraction
from pathlib import Path
import json
import mpmath as mp
import sympy as sp
from cm_norms import (H, X, reduced_forms, iv_eisenstein, polynomial_certificate,
                      iv_fraction, bounds, eis)

R = sp.Rational
DATA = {
    15: {'positive_discriminant':5, 'negative_discriminant':-3,
         'lambda':R(1,3), 'unit':(1+sp.sqrt(5))/2, 'A':R(1,2),
         'plus':[(1,1,4)],
         'factor':X+(191025+85995*sp.sqrt(5))/2,
         'ratio':(4+sp.sqrt(5))**2/44,
         'ratio6':(29+12*sp.sqrt(5))/88},
    20: {'positive_discriminant':5, 'negative_discriminant':-4,
         'lambda':R(1,2), 'unit':(1+sp.sqrt(5))/2, 'A':R(1,2),
         'plus':[(1,0,5)],
         'factor':X-632000-282880*sp.sqrt(5),
         'ratio':(3+2*sp.sqrt(5))**2/44,
         'ratio6':(601+252*sp.sqrt(5))/1672},
    39: {'positive_discriminant':13, 'negative_discriminant':-3,
         'lambda':R(1,3), 'unit':(3+sp.sqrt(13))/2, 'A':R(3,4),
         'plus':[(1,1,10),(3,3,4)],
         'factor':X**2+(165765798+45975573*sp.sqrt(13))*X
                    +(63399280527+17399806263*sp.sqrt(13))/2,
         'ratio':(103299+4440*sp.sqrt(13))/181424,
         'ratio6':(1323+324*sp.sqrt(13))/1472},
}

def conjugate(expr,k):
    return sp.expand(expr.xreplace({sp.sqrt(k):-sp.sqrt(k)}))

def iv_quad(expr,k):
    expr=sp.expand(expr)
    b=expr.coeff(sp.sqrt(k)); a=sp.simplify(expr-b*sp.sqrt(k))
    assert a.is_Rational and b.is_Rational
    return iv_fraction(Fraction(int(a.p),int(a.q))) + \
           iv_fraction(Fraction(int(b.p),int(b.q)))*mp.iv.sqrt(k)

def eval_iv_poly(poly,k,z):
    answer=mp.iv.mpc(0)
    for c in sp.Poly(poly,X).all_coeffs():
        answer=answer*z+iv_quad(c,k)
    return answer

def genus_value(form,e,d):
    """Find a represented integer coprime to D and evaluate the genus symbol."""
    from math import gcd
    a,b,c=form
    for height in range(1,10):
        for m in range(-height,height+1):
            for n in range(-height,height+1):
                value=a*m*m+b*m*n+c*n*n
                if value>0 and gcd(value,d)==1:
                    return int(sp.kronecker_symbol(e,value)), (m,n,value)
    raise AssertionError('No witness found')

def certificate(d,data):
    e=data['positive_discriminant']; hp=data['factor']; hm=conjugate(hp,e)
    assert sp.expand(hp*hm-H[d])==0
    # Fundamental-discriminant Kronecker symbols give L(0,chi) exactly.
    f=abs(data['negative_discriminant'])
    lzero=-sum(R(r,f)*sp.kronecker_symbol(-f,r) for r in range(1,f))
    assert lzero==data['lambda']
    forms=reduced_forms(d)
    labels=[]; actual_a=sp.Integer(1)
    for form in forms:
        eps,witness=genus_value(form,e,d)
        assert eps==(1 if form in data['plus'] else -1)
        actual_a*=sp.Integer(form[0])**eps
        z=iv_eisenstein(d,form)[3]
        wrong=hm if eps==1 else hp
        value=eval_iv_poly(wrong,e,z)
        real=bounds(value.real); imag=bounds(value.imag)
        exclusion=(real[1]<0 or real[0]>0 or imag[1]<0 or imag[0]>0)
        assert exclusion
        labels.append({'form':form,'genus_character':eps,'represented_witness':witness,
                       'wrong_factor_real_bounds':[str(x) for x in real],
                       'wrong_factor_imaginary_bounds':[str(x) for x in imag],
                       'wrong_factor_excludes_zero':True})
    assert actual_a==data['A']
    jratio=sp.simplify(hp.subs(X,0)/hm.subs(X,0))
    sign=sp.sign(jratio)
    assert sign in (-1,1)
    jratio=sp.simplify(sign*jratio)
    expected_cube=sp.simplify(data['A']**6 * data['unit']**(-12*data['lambda'])*jratio)
    assert sp.simplify(expected_cube-data['ratio']**3)==0
    assert data['ratio']>0
    ratio_norm=sp.simplify(data['ratio']*conjugate(data['ratio'],e))
    j6ratio=sp.simplify(hp.subs(X,1728)/hm.subs(X,1728))
    j6ratio=sp.simplify(sp.sign(j6ratio)*j6ratio)
    expected_square=sp.simplify(data['A']**6 * data['unit']**(-12*data['lambda'])*j6ratio)
    assert sp.simplify(expected_square-data['ratio6']**2)==0
    assert data['ratio6']>0
    return {'discriminant':-d,'positive_discriminant':e,
            'negative_discriminant':data['negative_discriminant'],
            'hilbert_polynomial_certificate':polynomial_certificate(d),
            'genus_plus_factor':str(hp),'genus_minus_factor':str(hm),
            'factorization_verified_exactly':True,'root_labels':labels,
            'leading_coefficient_ratio':str(actual_a),
            'lambda_exact':str(lzero),'unit':str(data['unit']),
            'absolute_j_product_ratio':str(jratio),
            'absolute_G4_product_ratio':str(sp.expand(data['ratio'])),
            'quadratic_norm_of_ratio':str(ratio_norm),
            'cubic_identity_verified_exactly':True,
            'absolute_G6_product_ratio':str(sp.expand(data['ratio6'])),
            'quadratic_norm_of_G6_ratio':str(sp.simplify(data['ratio6']*conjugate(data['ratio6'],e))),
            'square_identity_verified_exactly':True}

def regression(d,data,w):
    values={}
    for form in reduced_forms(d):
        a,b,c=form
        tau=mp.mpc(-mp.mpf(b)/(2*a),mp.sqrt(d)/(2*a))
        values[form]=2*mp.zeta(w)*eis(w,tau)
    actual=mp.fprod(abs(value)**(1 if form in data['plus'] else -1)
                    for form,value in values.items())
    expected=mp.mpf(str(sp.N(data['ratio'] if w==4 else data['ratio6'],mp.mp.dps)))
    residual=abs(actual-expected)/expected
    special=None
    if d==15:
        # On the unit arc, Re G4=(7/8)|G4| and Re G6=(11/16)|G6|.
        phase=mp.mpf(7)/8 if w==4 else mp.mpf(11)/16
        special=mp.nstr(abs(values[(1,1,4)]/values[(2,1,2)].real
                           -expected/phase)/(expected/phase),8)
    return {'discriminant':-d,'weight':w,'dps':mp.mp.dps,
            'absolute_ratio':mp.nstr(actual,35),
            'relative_residual':mp.nstr(residual,8),
            'D15_real_part_ratio_relative_residual':special}

def main():
    mp.iv.dps=120; mp.mp.dps=120
    results=[certificate(d,data) for d,data in DATA.items()]
    checks=[regression(d,data,w) for d,data in DATA.items() for w in (4,6)]
    dest=Path(__file__).with_name('cm_genus_receipt.json')
    dest.write_text(json.dumps({'engine':{'mpmath':mp.__version__,'sympy':sp.__version__},
                               'exact_and_interval_certificates':results,
                               'numerical_regressions':checks},indent=2)+'\n')
    for result in results:
        print(result['discriminant'],'factorization, genus labels, cube, and square certified')
    for check in checks:
        print('row regression',check['discriminant'],check['weight'],check['relative_residual'])
    print('receipt',dest)

if __name__=='__main__':main()
