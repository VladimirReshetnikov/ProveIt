#!/usr/bin/env python3
"""Independent verification of the mixed sixth-weight finite-part coordinate.

No functions are imported from the proposed implementation. Exact pole
coefficients come from a fresh Laurent expansion. Finite strict harmonic sums
verify the supplied spectral words independently of their stuffle generator.
The numerical integral uses a convergent Taylor series at zero plus quadrature;
the residue coordinate uses an unrelated asymptotic expansion and Hurwitz-zeta
derivatives to sum the tail. Numerical checks are diagnostics, not proofs.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import json
from pathlib import Path

import mpmath as mp
import sympy as sp

HERE = Path(__file__).resolve().parent
# Support both this research-work directory and a copy into the final bundle's
# code/ directory without needing to import any implementation being audited.
DATA_CANDIDATES = [HERE.parent / 'data/mixed_sixth_coordinates.json',
                   HERE.parent / 'output/polygamma_tail_research/data/mixed_sixth_coordinates.json']
DATA = next((p for p in DATA_CANDIDATES if p.exists()), DATA_CANDIDATES[0])


def exact_audit():
    data = json.loads(DATA.read_text())
    t = sp.Symbol('t')
    b, c, d, e, f, k = sp.symbols('b c d e f k')
    g = sp.Symbol('g')
    z = {j: sp.Symbol('z' + str(j)) for j in range(2, 8)}
    psi = -1/t + b+c*t+d*t**2+e*t**3+f*t**4+k*t**5
    prod = sp.expand(psi**2 * sp.diff(psi, t)**2)
    generic = {j: prod.coeff(t, -j) for j in range(1, 7)}
    for j in generic:
        assert sp.expand(generic[j]-sp.sympify(data['pole_coefficients'][str(j)])) == 0
    ct = sp.expand(prod.coeff(t, 0).subs(
        {b:-g, c:z[2], d:-z[3], e:z[4], f:-z[5], k:z[6]}))
    assert sp.expand(ct-sp.sympify(data['local_constant_at_zero'])) == 0
    hs = sp.symbols('h1:6')
    v = sp.Symbol('v')
    subst = {b:hs[0]-g,c:hs[1]+z[2],d:hs[2]-z[3],
             e:hs[3]+z[4],f:hs[4]-z[5]}
    poles = {j:sp.expand(generic[j].subs(subst)) for j in generic}
    delta = {j:sp.expand(p.subs({h:h+v**r for r,h in enumerate(hs,1)},
                               simultaneous=True)-p) for j,p in poles.items()}
    assert sp.expand(delta[1]-sp.sympify(data['delta_residue_polynomial'])) == 0
    jpoly = sp.expand(sum(delta[j]*v**(j-1)/sp.Integer(j-1) for j in range(2,7)))

    # These polynomials have harmonic degree at most two, so their conversion
    # needs only H_a H_b = H_(a,b)+H_(b,a)+H_(a+b), with no recursive stuffle.
    def direct_degree_two_conversion(poly):
        out={}
        for powers,coeff in sp.Poly(poly,*hs,v).terms():
            letters=tuple(r for r,power in enumerate(powers[:-1],1) for _ in range(power))
            assert len(letters)<=2
            if len(letters)==2:
                words=[letters,letters[::-1],(sum(letters),)]
            else:
                words=[letters]
            for word in words:
                key=(powers[-1],)+word
                out[key]=out.get(key,0)+coeff
        return {key:sp.expand(c) for key,c in out.items() if sp.expand(c)!=0}

    for key,target in [('spectral_words',delta[1]),('higher_pole_words',jpoly)]:
        actual=direct_degree_two_conversion(target)
        expected={tuple(row['word']):sp.sympify(row['coefficient']) for row in data[key]}
        assert actual.keys()==expected.keys()
        assert all(sp.expand(actual[word]-expected[word])==0 for word in actual)

    @lru_cache(None)
    def strict_harmonic(n, word):
        if not word:
            return sp.Integer(1)
        return sum((sp.Rational(1,k**word[0])*strict_harmonic(k-1,word[1:])
                    for k in range(1,n+1)),sp.Integer(0))

    # Exact rational finite sums test the supplied word coordinates, with the
    # constants gamma and zeta values kept as independent symbols.
    for n in range(1, 13):
        point = {v:sp.Rational(1,n)}
        point.update({h:strict_harmonic(n-1,(r,)) for r,h in enumerate(hs,1)})
        for key,target in [('spectral_words',delta[1]),('higher_pole_words',jpoly)]:
            val = sum((sp.sympify(row['coefficient'])*sp.Rational(1,n**row['word'][0])
                       *strict_harmonic(n-1,tuple(row['word'][1:]))
                       for row in data[key]),sp.Integer(0))
            assert sp.expand(val-target.subs(point)) == 0

    # Derive the needed weight-five values from three standard exact identities
    # instead of importing the proposed table of MZV evaluations.
    z41,z32,z23=sp.symbols('Z41 Z32 Z23')
    weight_five=sp.solve([z41+z32+z23-z[5],
                         z32+z23+z[5]-z[2]*z[3],
                         6*z41+3*z32+z23-z[2]*z[3]],(z41,z32,z23))
    z31,z22=sp.symbols('Z31 Z22')
    weight_four=sp.solve([2*z22+z[4]-z[2]**2,
                         4*z31+2*z22-z[2]**2],(z31,z22))
    values={(2,1):z[3],(3,1):weight_four[z31],(2,2):weight_four[z22],
            (4,1):weight_five[z41],(3,2):weight_five[z32],
            (2,3):weight_five[z23],(3,1,1):weight_five[z41],
            (2,2,1):weight_five[z32],(2,1,2):weight_five[z23]}
    jreduced=sp.expand(sum(sp.sympify(row['coefficient'])*
                  (z[row['word'][0]] if len(row['word'])==1 else values[tuple(row['word'])])
                  for row in data['higher_pole_words']))
    jreduced=sp.expand(jreduced.subs(z[2]**2,sp.Rational(5,2)*z[4]))
    assert sp.expand(jreduced-sp.sympify(data['higher_pole_sum']))==0

    # Check the wholly convergent replacement by finite exact ordering sums.
    tail_checks=0
    for N in range(1,7):
        def tail(r,n):
            return strict_harmonic(N,(r,))-strict_harmonic(n-1,(r,))
        for tpower in range(1,4):
            ordinary=sum(sp.Rational(1,n**tpower)*tail(2,n) for n in range(1,N+1))
            assert ordinary==strict_harmonic(N,(2,tpower))+strict_harmonic(N,(2+tpower,))
            mixed=sum(sp.Rational(1,n**tpower)*strict_harmonic(n-1,(1,))*tail(3,n)
                      for n in range(1,N+1))
            assert mixed==strict_harmonic(N,(3,tpower,1))+strict_harmonic(N,(3+tpower,1))
            square=sum(sp.Rational(1,n**tpower)*tail(2,n)**2 for n in range(1,N+1))
            assert square==(2*strict_harmonic(N,(2,2,tpower))
                           +2*strict_harmonic(N,(2,2+tpower))
                           +strict_harmonic(N,(4,tpower))+strict_harmonic(N,(4+tpower,)))
            tail_checks+=3

    return {'generic_poles_verified':6,'local_constant_verified':True,
            'delta_residue_verified':True,'word_tables_verified_formally':2,
            'exact_finite_harmonic_checks':24,'higher_pole_reduction_verified':True,
            'exact_tail_ordering_checks':tail_checks}


# Asymptotic polynomials have keys (k,r) for n^(-k) log(n)^r.
def add(*polys):
    out={}
    for p in polys:
        for key,c in p.items():
            out[key]=out.get(key,mp.mpf(0))+c
    return {key:c for key,c in out.items() if c}


def scale(a,p):
    return {key:a*c for key,c in p.items() if a*c}


def mul(a,b,order):
    out={}
    for (j,r),c in a.items():
        for (k,s),d in b.items():
            if j+k<=order:
                key=(j+k,r+s)
                out[key]=out.get(key,mp.mpf(0))+c*d
    return {key:c for key,c in out.items() if c}


def derivative(p,order):
    out={}
    for (j,r),c in p.items():
        if j+1<=order:
            if j:
                out[(j+1,r)]=out.get((j+1,r),mp.mpf(0))-j*c
            if r:
                out[(j+1,r-1)]=out.get((j+1,r-1),mp.mpf(0))+r*c
    return {key:c for key,c in out.items() if c}


def psi_asymptotic(order):
    p={(0,1):mp.mpf(1),(1,0):mp.mpf('0.5')}
    for k in range(2,order+1,2):
        p[(k,0)]=-mp.bernoulli(k)/k
    out=[p]
    for _ in range(4):
        out.append(derivative(out[-1],order))
    return out


def residue_expansion(order):
    b,p1,p2,p3,p4=psi_asymptotic(order)
    m=lambda a,b:mul(a,b,order)
    return add(scale(2,m(m(b,b),p2)), scale(-8*mp.zeta(2),m(b,p1)),
               scale(2,m(b,m(p1,p1))),scale(-6*mp.zeta(2),p2),
               scale(3,m(p1,p2)),scale(mp.mpf(5)/3,m(b,p3)),scale(mp.mpf(1)/4,p4))


def higher_pole_expansion(order):
    b,p1,p2,p3,p4=psi_asymptotic(order)
    c=add({(0,0):2*mp.zeta(2)},scale(-1,p1))
    d=scale(mp.mpf('0.5'),p2)
    e=add({(0,0):2*mp.zeta(4)},scale(-mp.mpf(1)/6,p3))
    m=lambda a,b:mul(a,b,order)
    def poles(b,c,d,e):
        return {6:{(0,0):mp.mpf(1)},5:scale(-2,b),4:m(b,b),
                3:add(scale(-2,m(b,c)),scale(2,d)),
                2:add(scale(2,m(m(b,b),c)),scale(-2,m(c,c)),
                      scale(-6,m(b,d)),scale(4,e))}
    now=poles(b,c,d,e)
    previous=poles(add(b,{(1,0):-mp.mpf(1)}),add(c,{(2,0):-mp.mpf(1)}),
                   add(d,{(3,0):-mp.mpf(1)}),add(e,{(4,0):-mp.mpf(1)}))
    out={}
    for j in range(2,7):
        out=add(out,m(add(now[j],scale(-1,previous[j])),{(j-1,0):mp.mpf(1)/(j-1)}))
    return out


def sum_asymptotic_tail(poly,n):
    out=mp.mpf(0)
    for (k,r),c in sorted(poly.items()):
        assert k>=2
        if r==0:
            term=mp.zeta(k,n+1)
        else:
            term=(-1)**r*mp.diff(lambda s:mp.zeta(s,n+1),mp.mpf(k),r)
        out+=c*term
    return out


def stable_residue(n):
    b=mp.digamma(n+1)
    p1,p2,p3,p4=(mp.polygamma(j,n+1) for j in range(1,5))
    return (2*b*b*p2-8*mp.zeta(2)*b*p1+2*b*p1*p1-6*mp.zeta(2)*p2
            +3*p1*p2+mp.mpf(5)/3*b*p3+p4/4)


def pole_vector(n):
    b=mp.digamma(n+1)
    c=2*mp.zeta(2)-mp.polygamma(1,n+1)
    d=mp.polygamma(2,n+1)/2
    e=2*mp.zeta(4)-mp.polygamma(3,n+1)/6
    return {6:mp.mpf(1),5:-2*b,4:b*b,3:-2*b*c+2*d,
            2:2*b*b*c-2*c*c-6*b*d+4*e}


def numeric_residue_coordinate(n,order):
    logarithm={(k,0):mp.mpf((-1)**(k+1))/k for k in range(1,order+1)}
    asym=mul(residue_expansion(order),logarithm,order)
    initial=mp.fsum(stable_residue(k)*mp.log1p(mp.mpf(1)/k) for k in range(1,n+1))
    return initial+sum_asymptotic_tail(asym,n)


def numeric_higher_pole_sum(n,order):
    previous=pole_vector(0)
    block=[]
    for k in range(1,n+1):
        now=pole_vector(k)
        block.append(mp.fsum((now[j]-previous[j])/(j-1)/mp.mpf(k)**(j-1)
                             for j in range(2,7)))
        previous=now
    return mp.fsum(block)+sum_asymptotic_tail(higher_pole_expansion(order),n)


def numerical_integral(delta,degree):
    # x psi(x) and x^2 psi'(x) have convergent power series for |x|<1.
    p=[-mp.mpf(1),-mp.euler]
    q=[mp.mpf(1),mp.mpf(0)]
    for k in range(2,degree+1):
        p.append((-1)**k*mp.zeta(k))
        q.append((k-1)*(-1)**k*mp.zeta(k))
    def product(a,b):
        return [mp.fsum(a[j]*b[k-j] for j in range(k+1)) for k in range(degree+1)]
    co=product(product(p,p),product(q,q))
    local=mp.fsum(c*(mp.log(delta) if k==5 else delta**(k-5)/(k-5))
                   for k,c in enumerate(co))
    direct=mp.quad(lambda x:mp.digamma(x)**2*mp.polygamma(1,x)**2,
                   [delta,mp.mpf('0.25'),mp.mpf('0.5'),1])
    return local+direct


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--dps',type=int,default=90)
    parser.add_argument('--n',type=int,default=80)
    parser.add_argument('--order',type=int,default=60)
    parser.add_argument('--output',default=str(HERE.parent/'verification/mixed_sixth_audit.json'))
    args=parser.parse_args()
    mp.mp.dps=args.dps
    report={'exact_checks':exact_audit(),'precision_digits':args.dps,
            'sum_cutoff':args.n,'asymptotic_order':args.order}
    print('Exact local and finite harmonic checks passed.',flush=True)
    integral=numerical_integral(mp.mpf(1)/8,140)
    integral2=numerical_integral(mp.mpf(1)/10,130)
    print('I =',mp.nstr(integral,80),'quadrature check',mp.nstr(abs(integral-integral2),8),flush=True)
    omega=numeric_residue_coordinate(args.n,args.order)
    print('Omega =',mp.nstr(omega,80),flush=True)
    jclosed=(2*mp.euler**2*mp.zeta(3)-mp.mpf(35)/3*mp.euler*mp.zeta(4)
             +mp.mpf(31)/3*mp.zeta(2)*mp.zeta(3)-mp.mpf(19)/3*mp.zeta(5))
    jsum=numeric_higher_pole_sum(args.n,args.order)
    print('J =',mp.nstr(jclosed,80),'series error',mp.nstr(abs(jsum-jclosed),8),flush=True)
    print('I-J-Omega =',mp.nstr(integral-jclosed-omega,12),flush=True)
    rzero=stable_residue(0)
    dzero=(4*mp.euler**2*mp.zeta(3)-5*mp.euler*mp.zeta(4)
           -6*mp.zeta(2)*mp.zeta(3)+6*mp.zeta(5))
    report.update({k:mp.nstr(v,args.dps) for k,v in {
        'finite_part_integral':integral,'quadrature_difference':integral-integral2,
        'residue_coordinate':omega,'higher_pole_sum_closed':jclosed,
        'higher_pole_sum_direct':jsum,'higher_pole_sum_error':jsum-jclosed,
        'coordinate_identity_error':integral-jclosed-omega,
        'D_at_zero':dzero,'D_at_zero_telescoping_error':dzero+rzero}.items()})
    (HERE/args.output).write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':
    main()
