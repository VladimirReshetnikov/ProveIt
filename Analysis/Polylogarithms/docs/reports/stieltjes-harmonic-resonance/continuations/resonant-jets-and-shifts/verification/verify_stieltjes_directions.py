"""Reproducible exact and numerical checks for Sections 02--04.

Dependencies: Python 3.10+, sympy, mpmath.
Run: python verify_stieltjes_directions.py

Exact checks are finite symbolic/algebraic identities. Numerical checks
are diagnostics, not interval enclosures and not substitutes for proofs.
The script does not need the manuscript files or network access.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations
import json
import math
from pathlib import Path

import mpmath as mp
import sympy as sp


def partitions(items):
    """Emit each set partition once; elements inside each block are sorted."""
    items = tuple(items)
    if not items:
        yield ()
        return
    first, rest = items[0], items[1:]
    for part in partitions(rest):
        yield ((first,),) + part
        for i in range(len(part)):
            yield part[:i] + ((first,) + part[i],) + part[i + 1:]


def poly_mul(left, right):
    out = defaultdict(lambda: sp.Integer(0))
    for i, a in left.items():
        for j, b in right.items():
            out[i + j] += a * b
    return dict(out)


def curved_checks():
    e = sp.symbols('e')
    c1, c2, c3, d1, d2, d3 = sp.symbols('c1 c2 c3 d1 d2 d3')
    g0, g1, ca = sp.symbols('g0 g1 C_a')
    u = c1*e+c2*e**2+c3*e**3
    v = d1*e+d2*e**2+d3*e**3
    # Differentiate the regularized rational polar factors directly.
    regular_double = sp.cancel(1 / ((u/e) * ((u+v)/e)))
    regular_single = sp.cancel((g0-g1*v)/(u/e))
    actual = ca + sp.diff(regular_double,e,2).subs(e,0)/2 \
                + sp.diff(regular_single,e).subs(e,0)
    aa, bb, cc = c1+d1, c2+d2, c3+d3
    expected = ca-g1*d1/c1-g0*c2/c1**2 + (
        c2**2/c1**2+bb**2/aa**2+c2*bb/(c1*aa)-c3/c1-cc/aa)/(c1*aa)
    assert sp.cancel(actual-expected) == 0
    lam, alpha, beta = sp.symbols('lambda alpha beta')
    curved_example = expected.subs({c1:1,c2:0,c3:0,d1:1,d2:lam,d3:0})
    assert sp.expand(curved_example-(ca-g1+lam**2/8)) == 0
    reparam = expected.subs({c1:1,d1:1,c2:alpha,d2:alpha,c3:beta,d3:beta})
    assert sp.expand(reparam-(ca-g1-g0*alpha+(3*alpha**2-2*beta)/2)) == 0
    return {'checks':3,'general_symbolic_residual':'0',
            'same_tangent_example_residual':'0','diagonal_reparametrization_residual':'0'}


def depth_three_checks():
    g0,g1,g2,z2,z2p,z3 = sp.symbols('g0 g1 g2 z2 z2p z3')
    c = sp.symbols('c1 c2 c3', nonzero=True)
    singles = [{-1:1/x, 0:g0, 1:-g1*x, 2:g2*x*x/2} for x in c]
    triple = poly_mul(poly_mul(singles[0],singles[1]),singles[2])
    direct = triple[0] + 2*z3
    for i in range(3):
        pair = {0:z2,1:(sum(c)-c[i])*z2p}
        direct -= poly_mul(singles[i],pair)[0]
    printed = (g0**3-g0*g1*sum(c[j]/c[i] for i in range(3) for j in range(3) if i!=j)
               +g2/2*sum(c[i]**2/(c[(i+1)%3]*c[(i+2)%3]) for i in range(3))
               -3*g0*z2-z2p*sum((sum(c)-c[i])/c[i] for i in range(3))+2*z3)
    assert sp.cancel(direct-printed)==0
    directions=[(1,2,3),(1,2,-3),(1,-1,2),(1,1,1),
                (sp.Rational(2,3),-sp.Rational(4,5),sp.Rational(7,6)),
                (1,sp.I,1+sp.I),(2,-3,1),(1,-1,-2)]
    rows=[]
    for direction in directions:
        subs=dict(zip(c,direction))
        assert sp.simplify((direct-printed).subs(subs))==0
        rows.append({'direction':[str(x) for x in direction],'residual':'0'})
    return {'checks':1+len(rows),'general_symbolic_residual':'0','nonunit_direction_checks':rows}


class MultiQuad:
    """Exact Q-linear sums of sqrt(d), d positive squarefree integers."""
    def __init__(self, terms=None):
        self.terms={d:Fraction(c) for d,c in (terms or {}).items() if c}

    @staticmethod
    def rational(x):
        return MultiQuad({1:Fraction(x)})

    def __add__(self, other):
        terms=defaultdict(Fraction,self.terms)
        for d,c in other.terms.items():
            terms[d]+=c
        return MultiQuad(terms)

    def __mul__(self, other):
        terms=defaultdict(Fraction)
        for a,ca in self.terms.items():
            for b,cb in other.terms.items():
                g=math.gcd(a,b)
                terms[a*b//(g*g)]+=ca*cb*g
        return MultiQuad(terms)

    def scale(self, q):
        return MultiQuad({d:c*q for d,c in self.terms.items()})

    def __eq__(self,other):
        return self.terms==other.terms


def square_part(n):
    coefficient=1
    squarefree=1
    p=2
    while p*p<=n:
        exponent=0
        while n%p==0:
            n//=p
            exponent+=1
        coefficient*=p**(exponent//2)
        if exponent%2:
            squarefree*=p
        p+=1
    if n>1:
        squarefree*=n
    return coefficient,squarefree


@lru_cache(None)
def reciprocal_half_power(x, exponent):
    """Exact x^(-exponent) for positive rational x and half-integer exponent."""
    x,exponent=Fraction(x),Fraction(exponent)
    twice=2*exponent
    assert twice.denominator==1 and twice>=0
    k=twice.numerator
    p,q=x.numerator,x.denominator
    if k%2==0:
        return MultiQuad.rational(Fraction(q,p)**(k//2))
    factor,sf=square_part(p*q)
    coefficient=Fraction(q,p)**(k//2)*Fraction(factor,p)
    return MultiQuad({sf:coefficient})


def finite_partition_checks():
    rows=[]
    tuples_total=0
    for depth in range(2,6):
        cutoff=depth+2
        patterns=[tuple(Fraction(i+1,2) for i in range(depth)),
                  tuple(Fraction(1 if i%2==0 else 3,2) for i in range(depth))]
        for shift in [Fraction(1),Fraction(1,2)]:
            for exponents in patterns:
                # Independent left side: labelled distinct tuples, no partitions.
                direct=MultiQuad.rational(0)
                tuple_count=0
                for ns in permutations(range(cutoff),depth):
                    value=MultiQuad.rational(1)
                    for n,s in zip(ns,exponents):
                        value=value*reciprocal_half_power(n+shift,s)
                    direct=direct+value
                    tuple_count+=1
                # Right side: finite equality-block power sums.
                block_cache={}
                def power_sum(s):
                    if s not in block_cache:
                        value=MultiQuad.rational(0)
                        for n in range(cutoff):
                            value=value+reciprocal_half_power(n+shift,s)
                        block_cache[s]=value
                    return block_cache[s]
                rhs=MultiQuad.rational(0)
                partition_count=0
                for part in partitions(range(depth)):
                    value=MultiQuad.rational((-1)**(depth-len(part)))
                    for block in part:
                        value=value*power_sum(sum(exponents[i] for i in block)).scale(math.factorial(len(block)-1))
                    rhs=rhs+value
                    partition_count+=1
                assert direct==rhs
                tuples_total+=tuple_count
                rows.append({'depth':depth,'cutoff':cutoff,'shift':str(shift),
                             'exponents':[str(x) for x in exponents],
                             'distinct_labelled_tuples':tuple_count,'set_partitions':partition_count,
                             'radical_basis_terms':len(direct.terms),'exact_residual':'0'})
    return {'checks':len(rows),'total_distinct_labelled_tuples':tuples_total,'cases':rows}


def regular_jet_checks():
    u,v=sp.symbols('u v')
    gam=sp.symbols('gamma0:8')
    zd=sp.symbols('zeta2der0:7')
    def g(x):
        return sum((-1)**k*gam[k]*x**k/sp.factorial(k) for k in range(8))
    core=sp.Poly(sp.expand(g(u)*g(v)+(g(u)-g(u+v))/v
                         -sum(zd[k]*(u+v)**k/(2*sp.factorial(k)) for k in range(7))),u,v)
    count=0
    for m in range(4):
        for n in range(4):
            smn=sp.symbols(f'S_{m}_{n}')
            actual=core.coeff_monomial(u**m*v**n)-(-1)**(m+n)*smn/(sp.factorial(m)*sp.factorial(n))
            expected=((-1)**(m+n)/(sp.factorial(m)*sp.factorial(n))
                      *(gam[m]*gam[n]+gam[m+n+1]/(n+1)-smn)
                      -zd[m+n]/(2*sp.factorial(m)*sp.factorial(n)))
            assert sp.expand(actual-expected)==0
            count+=1
    return {'checks':count,'m_range':[0,3],'n_range':[0,3],'all_exact_residuals':'0'}


@lru_cache(None)
def stieltjes_integral(index, shift):
    """Hermite integral, independent of the discrete shift recurrence."""
    a=mp.mpf(shift)
    if index==0:
        return -mp.digamma(a)
    la=mp.log(a)
    def integrand(t):
        if not t:
            return (index*la**(index-1)-la**index)/(2*mp.pi*a*a)
        z=a+1j*t
        return mp.im(mp.log(z)**index/z)/mp.expm1(2*mp.pi*t)
    return la**index/(2*a)-la**(index+1)/(index+1)-2*mp.quad(integrand,[0,1,4,mp.inf])


@lru_cache(None)
def stieltjes_endpoint(index, shift):
    a=mp.mpf(shift)
    return -mp.digamma(a) if index==0 else mp.stieltjes(index,a)


def stieltjes_tail_checks():
    cases=[((0,0),'1',5),((0,0,0),'0.5',4),((0,1),'1',3),
           ((1,1),'1.5',3),((0,0,1),'0.5',3),((0,0,0,0),'1',5)]
    rows=[]
    for indices,astr,n_terms in cases:
        a=mp.mpf(astr)
        degree=len(indices)
        kk=sum(p+1 for p in indices)
        aa=math.prod(p+1 for p in indices)
        correction=mp.mpf((-1)**degree*kk)/aa
        grouped=[]
        for n in range(n_terms):
            x=a+n
            lx=mp.log(x)
            gs=[stieltjes_integral(p,str(x)) for p in indices]
            value=correction*lx**(kk-1)/x
            for size in range(1,degree+1):
                for subset in combinations(range(degree),size):
                    chosen=set(subset)
                    term=(-1)**(size+1)*lx**sum(indices[i] for i in chosen)/x**size
                    for j in range(degree):
                        if j not in chosen:
                            term*=gs[j]
                    value+=term
            grouped.append(value)
        def endpoint_f(x):
            return mp.fprod(stieltjes_endpoint(p,str(x)) for p in indices) \
                  +correction*stieltjes_endpoint(kk-1,str(x))
        fa,tail=endpoint_f(a),endpoint_f(a+n_terms)
        prefix=mp.fsum(grouped)
        residual=abs(prefix+tail-fa)
        assert residual<mp.mpf('1e-45')
        rows.append({'indices':list(indices),'a':astr,'prefix_length':n_terms,
                     'prefix':mp.nstr(prefix,45),'independently_evaluated_tail':mp.nstr(tail,45),
                     'initial_product_correction':mp.nstr(fa,45),
                     'absolute_residual':mp.nstr(residual,9)})
    return {'checks':len(rows),'summand_method':'Hermite integral; digamma at index zero',
            'endpoint_method':'cached mpmath.stieltjes, maximum index three',
            'cases':rows}


def double_zeta_em(s,t,a,cutoff=64,terms=16):
    """Independent finite outer sum with an Euler--Maclaurin tail.

    This is a numerical approximation. Agreement after varying cutoff and
    terms is a stability diagnostic, not a certified error bound.
    """
    inner=mp.mpc(0)
    prefix=mp.mpc(0)
    for n in range(cutoff):
        x=n+a
        prefix+=x**(-s)*inner
        inner+=x**(-t)
    aa=a+cutoff
    if t==1:
        tail=-mp.digamma(a)*mp.zeta(s,aa)-mp.diff(lambda ss:mp.zeta(ss,aa),s)
        tail-=mp.zeta(s+1,aa)/2
        for k in range(1,terms+1):
            tail-=mp.bernoulli(2*k)/(2*k)*mp.zeta(s+2*k,aa)
    else:
        tail=mp.zeta(t,a)*mp.zeta(s,aa)-mp.zeta(s+t-1,aa)/(t-1)
        tail-=mp.zeta(s+t,aa)/2
        rising=t
        for k in range(1,terms+1):
            if k>1:
                rising*= (t+2*k-3)*(t+2*k-2)
            tail-=mp.bernoulli(2*k)/mp.factorial(2*k)*rising*mp.zeta(s+t+2*k-1,aa)
    return prefix+tail


def directional_checks():
    a=mp.mpf(1)
    g0=stieltjes_endpoint(0,'1')
    g1=stieltjes_endpoint(1,'1')
    ca=(g0*g0-mp.zeta(2,a))/2
    curves=[('straight_1_2',(1,0,0),(2,0,0)),
            ('straight_2_minus1',(2,0,0),(-1,0,0)),
            ('curved_same_diagonal_tangent',(1,0,0),(1,3,0))]
    radius=mp.mpf('0.02')
    nodes=32
    rows=[]
    stability=[]
    for name,cs,ds in curves:
        def uv(e):
            return (mp.fsum(c*e**(j+1) for j,c in enumerate(cs)),
                    mp.fsum(d*e**(j+1) for j,d in enumerate(ds)))
        values=[]
        for k in range(nodes):
            e=radius*mp.exp(2j*mp.pi*(k+mp.mpf('0.317'))/nodes)
            u,v=uv(e)
            values.append(double_zeta_em(1+u,1+v,a))
        numerical_constant=mp.fsum(values)/nodes
        c1,c2,c3=map(mp.mpf,cs)
        d1,d2,d3=map(mp.mpf,ds)
        aa,bb,cc=c1+d1,c2+d2,c3+d3
        expected=ca-g1*d1/c1-g0*c2/c1**2+(
            c2*c2/(c1*c1)+bb*bb/(aa*aa)+c2*bb/(c1*aa)-c3/c1-cc/aa)/(c1*aa)
        residual=abs(numerical_constant-expected)
        assert residual<mp.mpf('1e-35')
        rows.append({'curve':name,'u_coefficients':list(cs),'v_coefficients':list(ds),
                     'cauchy_constant':mp.nstr(numerical_constant,43),
                     'expected_constant':mp.nstr(expected,43),'absolute_residual':mp.nstr(residual,9)})
        u,v=uv(radius*(1+mp.j)/2)
        stab=abs(double_zeta_em(1+u,1+v,a,64,16)-double_zeta_em(1+u,1+v,a,80,20))
        assert stab<mp.mpf('1e-38')
        stability.append({'curve':name,'absolute_difference':mp.nstr(stab,9)})
    return {'checks':len(rows),'stability_checks':len(stability),
            'method':'discrete Cauchy coefficient extraction from an independent finite-sum EM evaluator',
            'cauchy_nodes':nodes,'cauchy_radius':str(radius),'EM_cutoff':64,'EM_terms':16,
            'cases':rows,'EM_stability':stability,
            'certified':False}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dps',type=int,default=60)
    parser.add_argument('--skip-directional',action='store_true',
                        help='Skip the slowest optional numerical coefficient diagnostics.')
    args=parser.parse_args()
    if args.dps<55:
        parser.error('Use at least 55 digits for the fixed numerical thresholds.')
    mp.mp.dps=args.dps
    report={'description':__doc__.split('\n')[0],
            'working_decimal_digits':args.dps,
            'versions':{'sympy':sp.__version__,'mpmath':mp.__version__},
            'numerical_results_are_diagnostics_not_certificates':True,
            'exact':{},'numerical':{}}
    for name,function in [('curved_paths',curved_checks),('depth_three_laurent',depth_three_checks),
                          ('finite_partition_identities',finite_partition_checks),('regular_jet_coefficients',regular_jet_checks)]:
        result=function()
        report['exact'][name]=result
        print(json.dumps({'completed':name,'exact_checks':result['checks']}),flush=True)
    result=stieltjes_tail_checks()
    report['numerical']['finite_stieltjes_products']=result
    print(json.dumps({'completed':'finite_stieltjes_products','numerical_checks':result['checks']}),flush=True)
    if not args.skip_directional:
        result=directional_checks()
        report['numerical']['directional_coefficients']=result
        print(json.dumps({'completed':'directional_coefficients','numerical_checks':result['checks'],
                          'stability_checks':result['stability_checks']}),flush=True)
    report['counts']={'exact_identity_checks':sum(r['checks'] for r in report['exact'].values()),
                      'numerical_identity_checks':sum(r['checks'] for r in report['numerical'].values()),
                      'numerical_stability_checks':sum(r.get('stability_checks',0) for r in report['numerical'].values()),
                      'finite_distinct_labelled_tuples':report['exact']['finite_partition_identities']['total_distinct_labelled_tuples']}
    output=Path(__file__).resolve().parent.parent/'results'/'verify_stieltjes_directions.json'
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'output':str(output),'counts':report['counts']}),flush=True)


if __name__=='__main__':
    main()
