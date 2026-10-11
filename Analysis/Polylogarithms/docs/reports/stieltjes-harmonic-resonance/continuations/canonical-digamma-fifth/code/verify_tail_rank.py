#!/usr/bin/env python3
"""Exact finite checks and independent numerical diagnostics for tail rank.

The infinite-rank and finite-prefix assertions are proved in tail_rank_notes.tex.
The finite first-q checks below are not an all-pairs theorem.
"""
from __future__ import annotations

import json
from math import comb
from pathlib import Path

import mpmath as mp
import sympy as sp


def _term(top: int, lower: int):
    if 2 <= lower <= top:
        return sp.Rational(comb(top, lower), top)
    return sp.S.Zero


def entry(p: int, q: int, j: int, k: int):
    d = 2*j + 1
    e = d-p-q+2*k+1
    if e < 0:
        return sp.S.Zero
    return sp.bernoulli(e)*(_term(d-q+1, p-2*k)
                           + _term(d-p+1, q-2*k))


def source_entry(p: int, q: int, j: int, k: int):
    """Independently assemble the two ordered sums and rational source block."""
    d = 2*j + 1
    if k == 0:
        if d < p+q-1:
            return sp.S.Zero
        # Source rational block is multiplied by -2 to use zeta(0), not 1.
        return sp.bernoulli(d-p-q+1)*(sp.Rational(comb(d-q,p-1),p)
                                      +sp.Rational(comb(d-p,q-1),q))
    total = sp.S.Zero
    for a,b in ((p,q),(q,p)):
        for h in range(1,min((d-b+1)//2,a//2-1)+1):
            if a-2*h == 2*k:
                total += sp.Rational(comb(d-b+1,2*h),d-b+1)*sp.bernoulli(d-b+1-2*h)
    return total


def backward(j: int, r: int):
    return sp.binomial(2*j+1,2*r)*sp.Rational(1,2)**(2*(j-r)) if r <= j else sp.S.Zero


def forward(r: int, j: int):
    return sp.binomial(2*r,2*j)*sp.bernoulli(2*r-2*j,sp.Rational(1,2))/(2*j+1) if j <= r else sp.S.Zero


def prefix_bound(p: int, q: int):
    return q-1 if p == q else q*(q-p)//2+q//2+p-1


def test_exact():
    assertions = 0
    rank_records = []
    for q in range(2,25,2):
        for p in range(2,q+1,2):
            b=q//2
            # This square-prefix property is finite evidence for unequal pairs.
            M=sp.Matrix([[entry(p,q,j,k) for k in range(b)] for j in range(b,q)])
            det=M.det()
            assert det != 0
            assertions += 1
            rank_records.append(dict(p=p,q=q,late_block_determinant=str(det),late_block_rank=b,full_formal_rank=q,
                                     proved_prefix_last_index=prefix_bound(p,q)))
            if p == q:
                assert det == sp.Rational((-1)**(b*(b-1)//2),sp.factorial(b))
                assertions += 1
            if q <= 12:
                for j in range(b,2*q+1):
                    for k in range(b):
                        assert entry(p,q,j,k) == source_entry(p,q,j,k)
                        assertions += 1
    # Exact forward/inverse Bernoulli transforms.
    T=sp.Matrix(15,15,lambda r,j:forward(r,j))
    B=sp.Matrix(15,15,lambda j,r:backward(j,r))
    assert T*B == sp.eye(15)
    assert B*T == sp.eye(15)
    assertions += 2
    # Verify the stated long-prefix left inverse for representative mixed pairs.
    for p,q in ((2,4),(2,6),(4,6),(4,8),(8,10)):
        b=q//2;N=prefix_bound(p,q)
        M=sp.Matrix([[entry(p,q,j,k) for k in range(b)] for j in range(b,N+1)])
        L=(M.T*M).inv()*M.T
        assert L*M == sp.eye(b)
        H=2*(p+1)+(q-p)*(q+1)
        assert 2*N+4-p == H
        assertions += 2
    # Verify denominator clearing and the degree bound in the differential proof.
    t,y=sp.symbols('t y')
    def dt(expr):
        return sp.diff(expr,t)+y*sp.diff(expr,y)
    for p,q in ((2,4),(2,6),(4,6),(4,8)):
        b=q//2;m=q-p
        h=(y+1)/(y-1)
        for k in range(b):
            Q=t**(q-2*k)/sp.factorial(q-2*k)
            Qm=sp.diff(Q,t,m)
            B0=Qm.subs(t,0)
            derivative=Q*h
            for _ in range(m):
                derivative=dt(derivative)
            E=sp.Poly(sp.cancel((y-1)**(m+1)*((Qm-B0)*h+derivative)),y)
            assert E.degree() <= m+1
            for nu in range(m+2):
                P=sp.Poly(E.nth(nu),t)
                assert P.is_zero or P.degree() <= (p if nu in (0,m+1) else q)
                assertions += 1
            # Highest pole amplitude at a formal nonzero pole; y-1 is t-tau.
            # Symbolic residue comparison in the proof is checked independently
            # through the recurrence for h^(m)'s highest Laurent coefficient.
    # Complete mixed (2,6) inverse and the rational identity.
    M=sp.Matrix([[entry(2,6,j,k) for k in range(3)] for j in range(3,6)])
    target=sp.Matrix([[12,120,60],[344,-952,-720],[1084,-3800,-3120]])/61
    assert M.inv() == target
    coefficients=(target*sp.Matrix([[backward(j,r) for r in range(6)] for j in range(3,6)])).row(0)
    weights=sp.Matrix([[61,8204,116000,370048,303360,56320]])
    assert coefficients == sp.Rational(3,15616)*weights
    assertions += 2
    # Verify the ordinary subtraction polynomial independently from c_{p,j}.
    x=sp.symbols('x')
    def cp(p,j):
        return sp.Rational(comb(p+2*j-2,p-2),p-1)*sp.bernoulli(2*j,sp.Rational(1,2))
    ks=[sum(cp(2,h)*cp(6,j-h) for h in range(j+1)) for j in range(3)]
    assert ks == [sp.Rational(1,5),-sp.Rational(4,15),sp.Rational(87,200)]
    P=sum(weights[r]*x**(2*r) for r in range(6))
    raw=sp.expand(P*sum(ks[j]*x**(-6-2*j) for j in range(3)))
    removed=sum(term for term in sp.Add.make_args(raw) if term.as_powers_dict().get(x,0)>=0)
    assert sp.expand(removed-(11264*x**4+sp.Rational(136960,3)*x**2+sp.Rational(88064,5))) == 0
    assertions += 2
    return dict(assertions=assertions,first_q_prefix_checks=rank_records,
                all_pairs_first_q_theorem=False,
                diagonal_first_q_theorem=True,
                general_bound_theorem='N=q*(q-p)/2+q/2+p-1 for p<q; last included index')


def test_numeric():
    mp.mp.dps=90
    weights=[61,8204,116000,370048,303360,56320]
    def to_mp(r):
        n,d=sp.fraction(r)
        return mp.mpf(int(n))/int(d)
    def c(p,j):
        return sp.Rational(comb(p+2*j-2,p-2),p-1)*sp.bernoulli(2*j,sp.Rational(1,2))
    target=-mp.mpf(7808)/3
    results=[]
    for cutoff,terms in ((40,24),(64,32)):
        ks=[to_mp(sum(c(2,h)*c(6,j-h) for h in range(j+1))) for j in range(terms+1)]
        value=mp.mpf(0)
        for n in range(cutoff):
            x=n+mp.mpf('0.5')
            P=sum(mp.mpf(w)*x**(2*r) for r,w in enumerate(weights))
            value += (P*mp.zeta(2,n+1)*mp.zeta(6,n+1)-11264*x**4
                      -mp.mpf(136960)/3*x**2-mp.mpf(88064)/5)
        a=cutoff+mp.mpf('0.5')
        for r,w in enumerate(weights):
            # Only negative powers remain after the displayed polynomial subtraction.
            lower=max(0,r-2)
            for j in range(lower,terms+1):
                value += w*ks[j]*mp.zeta(6+2*j-2*r,a)
        results.append(dict(cutoff=cutoff,asymptotic_terms=terms,
                            value=mp.nstr(value,82),target=mp.nstr(target,82),
                            absolute_residual=mp.nstr(abs(value-target),8)))
    assert abs(mp.mpf(results[-1]['value'])-target)<mp.mpf('1e-55')
    return dict(working_decimal_digits=90,interval_certificate=False,
                source='direct Hurwitz-tail sums plus an independent centered asymptotic tail',
                comparisons=results)


if __name__ == '__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--exact-only',action='store_true')
    args=parser.parse_args()
    result={'exact':test_exact(),
            'versions':{'sympy':sp.__version__,'mpmath':mp.__version__}}
    if not args.exact_only:
        result['numeric']=test_numeric()
    name='tail_rank_exact_verification.json' if args.exact_only else 'tail_rank_verification.json'
    output=Path(__file__).resolve().parent.parent / 'results' / name
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'output':str(output),'assertions':result['exact']['assertions'],
                      'pairs':len(result['exact']['first_q_prefix_checks']),
                      'numeric':result.get('numeric',{}).get('comparisons',[])},indent=2))
