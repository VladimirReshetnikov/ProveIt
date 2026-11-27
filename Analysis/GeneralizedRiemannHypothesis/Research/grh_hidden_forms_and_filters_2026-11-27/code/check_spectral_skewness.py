#!/usr/bin/env python3
"""Exact algebra and optional independent high-precision moment checks.

The proof is in papers/spectral_skewness.tex. Finite tests and floating-point solves
are supplementary evidence, not formal certification of the infinite theorem.
Usage: python3 check_spectral_skewness.py --numeric --output verification.json
Dependencies: sympy; mpmath (for --numeric).
"""
import argparse
import json
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import sympy as sp


def exact_checks():
    x, z = sp.symbols('x z')
    n, j = sp.symbols('n j', integer=True, positive=True)
    ell = sp.log(1-x)
    ab = -(x-2)**2*x**3/(4*ell**3) + (x-1)*(2-x)*x**2/(2*ell**2)
    expected = x**2/sp.Integer(6)-x**3/sp.Integer(4)+11*x**4/sp.Integer(120)
    assert sp.expand(sp.series(ab,x,0,5).removeO()-expected)==0
    checks = {'logarithm_series': True}
    ps = sp.summation(j*(n-j)*(n-2*j)**2,(j,1,n-1))
    target = n*(n-1)*(n-2)*(n+1)*(n+2)/30
    assert sp.simplify(ps-target)==0
    checks['symbolic_power_sum_for_arbitrary_n']=True
    an = -sp.Rational(1,120)*(1-(n+1)*(n+2)/((n-1)*(n-2)))
    assert sp.simplify(an-n/(20*(n-1)*(n-2)))==0
    checks['symbolic_final_coefficient_for_arbitrary_n']=True
    beta_count=0
    first_count=0
    for N in range(3,41):
        den=N*(N-1)*(N-2)
        # Divide out pi^3. The node derivative comes from the independent
        # binomial coefficient formula for B(z).
        b=sp.Poly(z*(1-z)*(z+1)**(N-3)/sp.Integer(2)**(N+1),z)
        for J in range(N+1):
            v=Fraction(J*(N-J)*(N-2*J),2*den)
            coeff=b.nth(J)*2**N/sp.Integer(comb(N,J))
            assert coeff==sp.Rational(v.numerator,v.denominator)
            first_count+=1
        # Exact beta-integral coefficient, with no floating point.
        sc=Fraction(0)
        for J in range(1,N):
            direct=-sum((Fraction((-1)**(J-1-L)*comb(J-1,L),N-1-L)
                         for L in range(J)),Fraction(0))
            beta=-Fraction(factorial(N-J-1)*factorial(J-1),factorial(N-1))
            assert direct==beta
            v=Fraction(J*(N-J)*(N-2*J),2*den)
            cj=Fraction(comb(N,J),2**N)*v*v
            sc+=cj*beta
            beta_count+=1
        predicted_sc=-Fraction((N+1)*(N+2),120*2**N*(N-1)*(N-2))
        assert sc==predicted_sc
        sab=Fraction(1,120*2**N)
        an=-(2**N)*(sc+sab)
        assert an==Fraction(N,20*(N-1)*(N-2))
    checks.update(first_variation_identities=first_count,
                  beta_coefficient_identities=beta_count,
                  exact_n_range=[3,40])
    return checks


def solve_cluster(targets, dps=100):
    """Solve centered N+1-atom moment equations, without asymptotic inputs."""
    import mpmath as mp
    mp.mp.dps=dps
    N=len(targets)
    targets=sorted(mp.mpf(t) for t in targets)
    k=N//2
    if N%2:
        nodes0=[mp.pi*(j+mp.mpf('.5')) for j in range(k+1)]
        weights0=[mp.mpf(2*comb(N,k-j))/2**N for j in range(k+1)]
        pairs=k+1
        initial=nodes0+weights0[:-1]
    else:
        nodes0=[mp.pi*j for j in range(1,k+1)]
        weights0=[mp.mpf(2*comb(N,k-j))/2**N for j in range(1,k+1)]
        pairs=k
        initial=nodes0+weights0
    def unpack(parameters):
        parameters=list(parameters)
        nodes=parameters[:pairs]
        ws=parameters[pairs:]
        if N%2:
            ws=(*ws,1-sum(ws)); w0=mp.mpf(0)
        else:
            w0=1-sum(ws)
        return nodes,ws,w0
    def equations(*parameters):
        nodes,ws,w0=unpack(parameters)
        def F(x,d=0):
            out=sum(w*a**d*mp.cos(a*x+d*mp.pi/2) for a,w in zip(nodes,ws))
            return out+(w0 if d==0 else 0)
        # Hermite divided differences handle repeated frequencies exactly.
        table=[[F(t) for t in targets]]
        answer=[table[0][0]]
        for d in range(1,N):
            row=[]
            for i in range(N-d):
                if targets[i+d]==targets[i]:
                    row.append(F(targets[i],d)/mp.factorial(d))
                else:
                    row.append((table[d-1][i+1]-table[d-1][i])/
                               (targets[i+d]-targets[i]))
            table.append(row);answer.append(row[0])
        return tuple(answer)
    result=mp.findroot(equations,initial,tol=mp.mpf('1e-85'),maxsteps=30)
    nodes,ws,w0=unpack(result)
    residual=max(abs(v) for v in equations(*result))
    assert residual<mp.mpf('1e-70')
    assert all(w>0 for w in ws)
    assert N%2 or w0>0
    assert all(nodes[j]>0 and (j==0 or nodes[j]>nodes[j-1]) for j in range(pairs))
    mean=sum(targets)/N
    delta=[t/mean-1 for t in targets]
    p3=sum(t**3 for t in delta)
    width=2*nodes[-1]
    excess=width-N*mp.pi/mean
    leading=N*mp.pi**5/(180*(N-1)*(N-2)*mean)*p3*p3
    return {'N':N,'targets':[mp.nstr(t,30) for t in targets],
            'width':mp.nstr(width,50),'excess':mp.nstr(excess,40),
            'leading_term':mp.nstr(leading,40),
            'excess_over_leading':mp.nstr(excess/leading,30) if leading else None,
            'moment_residual':mp.nstr(residual,8),
            'minimum_atom_mass':mp.nstr(min([w/2 for w in ws]+([w0] if not N%2 else [])),20)}


def numerical_checks():
    import mpmath as mp
    mp.mp.dps=100
    rows=[]
    for N in range(3,11):
        for eps_text in ['0.01','0.005','0.002']:
            e=mp.mpf(eps_text)
            targets=[mp.mpf(1)]*(N-3)+[1-e]*2+[1+2*e]
            row=solve_cluster(targets)
            row['family']='two repeated shifts, remaining central'
            row['epsilon']=eps_text
            assert abs(mp.mpf(row['excess_over_leading'])-1)<mp.mpf('.005')
            rows.append(row)
    # Genuinely distinct real frequencies, independent of the repeated-root family.
    for shifts in [[-2,-1,3],[-3,-2,1,4],[-6,-3,-1,2,8]]:
        e=mp.mpf('.001')
        row=solve_cluster([1+e*t for t in shifts])
        row['family']='distinct asymmetric shifts';row['shifts']=shifts
        assert abs(mp.mpf(row['excess_over_leading'])-1)<mp.mpf('.005')
        rows.append(row)
    return {'precision_decimal_digits':100,'cases':rows,
            'status':'floating-point checks; not interval certificates'}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--numeric',action='store_true')
    ap.add_argument('--output',default=str(Path(__file__).resolve().parents[1] / 'data' / 'spectral_skewness_verification.json'))
    args=ap.parse_args()
    result={'theorem':'Sixth-order skewness penalty for shortest positive filters',
            'exact':exact_checks(),
            'proof_status':'human-readable proof; no Lean formalization claimed'}
    if args.numeric:result['numerical']=numerical_checks()
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: exact symbolic identities for arbitrary N and finite checks N=3..40.')
    if args.numeric:
        print(f"PASS: {len(result['numerical']['cases'])} independent high-precision moment solutions.")
    print('Recorded:',args.output)

if __name__=='__main__':main()
