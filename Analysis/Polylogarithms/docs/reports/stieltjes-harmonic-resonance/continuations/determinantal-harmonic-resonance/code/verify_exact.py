#!/usr/bin/env python3
"""Finite exact assertions supplementing, not replacing, the article's proofs."""
from __future__ import annotations
import itertools, json, math, pathlib, sys
import sympy as s
from reductions import N,m,H,u,z,L,D,moment,cutoff,maximum_mass,rational_partition,generating,endpoint
ROOT=pathlib.Path(__file__).resolve().parents[1]
counts={}
def check(kind,cond):
    if not bool(cond):
        raise AssertionError(kind)
    counts[kind]=counts.get(kind,0)+1

def weight(n,r):
    return 1/s.rf(s.Integer(n+1),2*r-1)

def direct(r,top):
    return sum(s.prod((a[j]-a[i])**2 for i in range(r) for j in range(i+1,r))
               *s.prod(weight(n,r) for n in a)
               for a in itertools.combinations(range(top+1),r))

# Rational determinant lemma, using non-arithmetic nodes as well as arithmetic nodes.
for r in range(1,7):
    for t in [s.Rational(2,3),s.Rational(5,2),s.Rational(-1,3)]:
        xs=[s.Rational((i+1)**2+1,i+2) for i in range(r)]
        mat=s.Matrix(r,r,lambda i,j:s.rf(xs[i],j)/s.rf(xs[i]+t,j))
        rhs=s.prod(s.rf(t,j) for j in range(r))*s.prod(xs[j]-xs[i] for i in range(r) for j in range(i+1,r))/s.prod(s.rf(x+t,r-1) for x in xs)
        check('rational_determinant_lemma',s.cancel(mat.det()-rhs)==0)

# Infinite moment determinant vs Gamma product at positive integral parameters.
for r in range(1,5):
    for a,c,extra in [(1,1,3),(2,3,4),(3,2,5),(2,4,2)]:
        b=a+c+2*r-2+extra; d=b-a-c
        mat=s.Matrix(r,r,lambda i,j:s.gamma(a+i+j)*s.gamma(c+i)*s.gamma(d-i-j)/(s.gamma(b-a-j)*s.gamma(b-c)))
        rhs=s.prod(s.factorial(j)*s.gamma(a+j)*s.gamma(c+j)*s.gamma(d-r+1-j)/(s.gamma(b-a-j)*s.gamma(b-c-j)) for j in range(r))
        check('gauss_vandermonde_product',mat.det()==rhs)

records=[]
for r in range(1,5):
    A,B=cutoff(r)
    for top in range(0,9):
        exact=direct(r,top)
        val=(A*s.harmonic(top+1)+B).subs(N,top)
        check('finite_ordered_sum_and_cutoff',s.cancel(exact-val)==0)
        mat=s.Matrix(r,r,lambda i,j:sum(s.Integer(n)**(i+j)*weight(n,r) for n in range(top+1)))
        check('finite_cauchy_binet',mat.det()==exact)
        for k in range(2*r-1):
            lhs=moment(r,k).subs({N:top,H:s.harmonic(top+1)})
            rhs=sum(s.Integer(n)**k*weight(n,r) for n in range(top+1))
            check('finite_moment_partial_fractions',s.cancel(lhs-rhs)==0)
    Fr=rational_partition(r)
    for uu in range(1,5):
        b=2*r+uu
        raw=s.prod(s.factorial(j)**3*s.gamma(r-1-j+uu)/s.gamma(2*r-1-j+uu)**2 for j in range(r))
        check('normalized_partition_rationality',Fr.subs(u,uu)==raw*(s.gamma(b)/s.gamma(2*r))**r)
    residue=s.limit(u*Fr,u,0)
    check('cutoff_residue',s.limit(A,N,s.oo)==residue)
    check('cutoff_constant',s.limit(B,N,s.oo)==-3*s.harmonic(r-1)*residue)
    item={'r':r,'cutoff_H_coefficient':str(A),'cutoff_rational_part':str(B),'rational_partition':str(Fr),'residue':str(residue),'generating_functions':{},'endpoint_values':{}}
    for q in range(0,4):
        g=s.expand(generating(r,q))
        item['generating_functions'][str(q)]=str(g)
        # Exact truncated power series in independent Li and Li_{p,1} symbols.
        length=15
        replacements={}
        for sym in g.free_symbols-{z}:
            p=int(str(sym)[1:])
            replacements[sym]=sum(z**n*(s.harmonic(n-1) if str(sym).startswith('D') else 1)/s.Integer(n)**p for n in range(1,length+12))
        series=s.expand(g.subs(replacements))
        mass=maximum_mass(r)
        for mm in range(1,length+1):
            expected=mass.subs({m:mm,H:s.harmonic(mm)})/s.Integer(mm)**q
            check('polylog_coefficients',s.cancel(series.coeff(z,mm)-expected)==0)
        for jj in range(-10,1):
            check('removable_origin_coefficients',s.cancel(series.coeff(z,jj))==0)
        if q:
            item['endpoint_values'][str(q)]=str(endpoint(r,q))
    records.append(item)

# A non-consecutive pole set: the general rank-one theorem is not tied to rising factorials.
for r,shifts in [(2,[1,3,5]),(3,[1,2,4,6,7])]:
    nn=s.symbols('nn')
    w=1/s.prod(nn+d for d in shifts)
    for k in range(2*r-1):
        coeffs=[s.cancel((nn+d)*nn**k*w).subs(nn,-d) for d in shifts]
        check('nonconsecutive_rank_one',sum(coeffs)==s.Integer(k==2*r-2))
        for top in [2,5,8]:
            formula=sum(c*(s.harmonic(top+d)-s.harmonic(d-1)) for c,d in zip(coeffs,shifts))
            check('nonconsecutive_moments',formula==sum((nn**k*w).subs(nn,n) for n in range(top+1)))

# Printed sample identities and an intentionally corrupted value.
check('printed_endpoint',s.simplify(endpoint(2,1)-(s.zeta(3)-s.pi**2/24-s.Rational(3,4)))==0)
check('printed_endpoint',s.simplify(endpoint(2,2)-(s.Rational(7,4)-s.pi**2/16-s.Rational(3,2)*s.zeta(3)+s.pi**4/144))==0)
check('printed_endpoint',s.simplify(endpoint(3,1)-(s.Rational(1903,124416)-s.Rational(35,62208)*s.pi**2-s.Rational(7,864)*s.zeta(3)))==0)
g2=generating(2)
expected=(z-1)**2/(2*z*z)*D(1)+(z-1)/(2*z)*L(2)+(6-5*z)/(4*z*z)*L(1)+s.Rational(3,4)-s.Rational(3,2)/z
check('printed_G2',s.expand(g2-expected)==0)
check('corruption_rejected',s.cancel(g2-(expected+z**2))!=0)

# Mixed harmonic moments: independently evaluate logarithmic derivatives of the Gamma product.
r=2; B=6
ell1=sum(s.polygamma(0,1+j)-s.polygamma(0,B-r-1-j)+s.polygamma(0,B-1-j) for j in range(r))-r*s.polygamma(0,1)
ellpp=sum(s.polygamma(1,1+j)+s.polygamma(1,B-r-1-j)-s.polygamma(1,B-1-j) for j in range(r))-r*s.polygamma(1,1)
ellpq=sum(s.polygamma(1,B-r-1-j) for j in range(r))
check('mixed_harmonic_coefficients',s.simplify(ell1-s.Rational(29,12))==0)
check('mixed_harmonic_coefficients',s.simplify(ellpp+s.Rational(67,144))==0)
check('mixed_harmonic_coefficients',s.simplify(ell1**2+ellpq-(s.Rational(517,144)+2*s.zeta(2)))==0)
check('mixed_harmonic_coefficients',s.simplify(ell1**2+ellpp-s.Rational(43,8))==0)

# First Stieltjes coefficient in the normalized two-particle case.
g,g1,Z2=s.symbols('gamma gamma1 Z2')
chi=g-3; E2=chi**2+3-Z2; a1=(s.Rational(5,3)-g)/4
D1=a1*(chi-g)+(E2/2+g1)/4
check('stieltjes_sample',s.expand(D1-(s.Rational(1,4)+(g*g-Z2)/8+g1/4))==0)

out={'status':'PASS','exact_assertions':sum(counts.values()),'categories':counts,'sympy_version':s.__version__,'scope':'Finite exact checks; all-index proofs are in article.tex.'}
(ROOT/'results'/'exact_checks.json').write_text(json.dumps(out,indent=2)+'\n')
(ROOT/'results'/'exact_formulas.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(out,indent=2))
