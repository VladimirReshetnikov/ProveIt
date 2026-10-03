#!/usr/bin/env python3
"""Run exact checks and regenerate numerical/symbolic data.

Usage: python code/verify.py [--order 12]
The default order 12 typically takes tens of seconds. No internet is used.
"""
from __future__ import annotations
import argparse
from collections import Counter
import csv
from itertools import permutations
from math import factorial
from pathlib import Path
import time
import sympy as sp
import mpmath as mp
from fixed_gap import (asymptotic_coefficients, avoidance, gap_lengths,
                       forest_profiles, moment_counts, stable_profile_count, histogram)

ROOT = Path(__file__).resolve().parents[1]
KNOWN = [1,1,2,5,18,75,410,2729,20906,181499,1763490,18943701,
         222822578,2847624899,39282739034,581701775369,9202313110506,
         154873904848803,2762800622799362,52071171437696453,
         1033855049655584786,21567640717569135515,471630531427793184474,
         10787660036599729160073,257590656485400508526570,
         6409633590481106885238443,165928838963556686281573922]
# Selected public b-file entries, retrieved 2026-10-01. Source in sources.md.
LARGE = {
20:1033855049655584786,
40:323050241764467120657010255773065347194505456938,
80:27324546049737112337970264116494822065047881773136488243489149490990078949136528308971283856759332392710909447370165482,
120:2522797078736501130924201221594287089274238057295045292325925264989150406463042940389675544509690131847479000174285660830480447102712205473096825508950373214966542978799957220339582273036907497226346,
}
POSTED_A = [1,3,2,1,0,3,26,101,124,-1409,-13266]
POSTED_B = list(map(sp.Rational, ['1','4','8','68/3','242/3','1692/5',
     '72802/45','2725708/315','16083826/315','186091480/567',
     '32213578294/14175']))


def run(order: int) -> None:
    start = time.perf_counter()
    lines: list[str] = []
    def report(text: str) -> None:
        print(text, flush=True)
        lines.append(text)

    pairs = [(1,1),(1,2),(2,2),(2,3),(3,3)]
    checked = 0
    for n in range(9):
        brute = Counter()
        brute_hist = Counter()
        for permutation in permutations(range(n)):
            for r, s in pairs:
                differences = [permutation[i+r]-permutation[i]
                               for i in range(max(0,n-r))]
                x1 = sum(d == s for d in differences)
                x2 = sum(abs(d) == s for d in differences)
                brute[r,s,1] += x1 == 0
                brute[r,s,2] += x2 == 0
                brute_hist[r,s,1,x1] += 1
                brute_hist[r,s,2,x2] += 1
        for r, s in pairs:
            for eta in (1,2):
                assert avoidance(n,r,s,eta) == brute[r,s,eta]
                assert histogram(gap_lengths(n,r),gap_lengths(n,s),eta) == [
                    brute_hist[r,s,eta,j] for j in range(n+1)]
                checked += 1
    report(f'PASS: {checked} brute-force avoidance and {checked} full-histogram comparisons, n=0..8.')

    for n, value in enumerate(KNOWN):
        assert avoidance(n,2,2) == value
    assert avoidance(40,2,2) == LARGE[40]
    report('PASS: independent exact tilings match A189281 for n=0..26 and n=40.')

    tests = 0
    for lengths in [(6,6),(5,7),(4,4,6),(6,8,10),(10,)]:
        actual = forest_profiles(lengths)
        # The profile dictionary contains all realizable cases; empty and dimer
        # cases include useful boundary and normalization controls.
        for profile, value in actual.items():
            k = sum(profile)-len(profile)
            if k <= min(lengths):
                assert stable_profile_count(sum(lengths),len(lengths),profile)==value
                tests += 1
    # A non-realizable profile must vanish in the stable range.
    assert stable_profile_count(7,1,(2,)*7)==0
    report(f'PASS: {tests} stable-profile identities, plus a zero-profile control.')

    for eta in (1,2):
        one = moment_counts((6,6),(6,6),eta)
        two = moment_counts((5,7),(4,8),eta)
        assert one[:5] == two[:5]
        assert one != two
    report('PASS: boundary universality through k=4 for unequal path balances; '
           'higher moments are not all identical.')

    # The directed one-path case has an independent contraction formula.
    from math import comb
    one_path_checks = 0
    for n in range(1,15):
        for s0 in range(1,min(4,n)+1):
            moments = moment_counts((n,),gap_lengths(n,s0),1)
            expected = [comb(n-s0,k)*factorial(n-k) if k<=n-s0 else 0
                        for k in range(n+1)]
            assert moments == expected
            one_path_checks += 1
    report(f'PASS: {one_path_checks} exact one-path contraction identities.')

    eta = sp.Symbol('eta')
    coefficients = asymptotic_coefficients(order,2,2,eta)
    a = [sp.factor(c.subs(eta,1)) for c in coefficients]
    b = [sp.factor(c.subs(eta,2)) for c in coefficients]
    assert a[:min(order+1,11)] == POSTED_A[:min(order+1,11)]
    assert b[:min(order+1,11)] == POSTED_B[:min(order+1,11)]
    assert not any(x.has(sp.Float) for x in a+b)
    if order >= 12:
        assert a[11:13] == [-59103,-9448]
        assert b[11:13] == [sp.Rational(2620164054016,155925),
                            sp.Rational(61699558213516,467775)]
    report(f'PASS: exact finite-defect coefficient engine through order {order}; '
           f'all posted coefficients through order {min(order,10)} reproduced.')

    r,s,z=sp.symbols('r s z')
    general={}
    for et in (1,2):
        general[et]=asymptotic_coefficients(3,r,s,et,z)
        assert sp.expand(general[et][1] -
                         (et*(1-et)*z*z-et*(r+s-1)*z)) == 0
        for j in (2,3):
            assert sp.expand(sp.diff(general[et][j],z).subs(z,0) - et*(r-1)*(s-1)) == 0
        assert all(c.subs(z,0)==0 for c in general[et][1:])
    assert [sp.factor(c.subs({r:2,s:2})) for c in general[1]] == [
        1,-3*z,z*(3*z+1),-z*(z*z-z-1)]
    report('PASS: general first-order pgf and exact-mean expansions through order 3.')

    # Verify the inverse corrections symbolically by matching the residual.
    t,D,d1,d2,d3 = sp.symbols('t D d1 d2 d3')
    A=sp.Rational(1,8)-d1
    u1=A/D
    u2=(sp.Rational(1,24)-d1/2-d2)/D
    u3=-(A*A/D+A*A/(2*D*D)+d1/4+d2+d3-sp.Rational(1,64))/D
    delta=-sp.Rational(1,2)+u1*t+u2*t*t+u3*t**3
    residual=(D*delta+delta**2*t/2-delta**3*t*t/6+delta**4*t**3/12
              +D/2+sp.log(1+t*delta)/2+d1*t/(1+t*delta)
              +d2*t*t/(1+t*delta)**2+d3*t**3/(1+t*delta)**3)
    assert sp.series(residual,t,0,4).removeO().expand().simplify()==0
    report('PASS: inverse-transseries residual vanishes through N^(-3).')

    data=ROOT/'data'; data.mkdir(exist_ok=True)
    with (data/'coefficients.csv').open('w',newline='') as f:
        writer=csv.writer(f);writer.writerow(['order','A189281','A110128'])
        writer.writerows((j,str(a[j]),str(b[j])) for j in range(order+1))
    (data/'component_weight_polynomials.txt').write_text('\n'.join(
        f'C_{j}(eta) = {c}' for j,c in enumerate(coefficients))+'\n')
    (data/'general_pgf_first_three.txt').write_text('\n'.join(
        f'eta={et}, C_{j} = {c}' for et in (1,2)
        for j,c in enumerate(general[et]))+'\n')

    mp.mp.dps=110
    rows=[]
    for n,value in LARGE.items():
        normalized=mp.e*mp.mpf(value)/mp.factorial(n)
        errors=[]
        for truncation in (2,5,10,12):
            if truncation<=order:
                approximation=sum(mp.mpf(str(a[j]))/mp.mpf(n)**j
                                  for j in range(truncation+1))
                errors.append(mp.nstr(normalized-approximation,16))
            else: errors.append('not computed')
        L=mp.log(value)+1-mp.log(2*mp.pi)/2
        w=mp.lambertw(L/mp.e); N=L/w; logN=1+w
        inverse=N-mp.mpf('0.5')-mp.mpf(71)/(24*N*logN)+1/(N*N*logN)
        rows.append([n,mp.nstr(normalized,20),*errors,mp.nstr(inverse-n,16)])
    with (data/'numerics.csv').open('w',newline='') as f:
        writer=csv.writer(f)
        writer.writerow(['n','e*a(n)/n!','error_M2','error_M5','error_M10',
                         'error_M12','inverse_minus_n'])
        writer.writerows(rows)
    with (data/'selected_oeis_values.csv').open('w',newline='') as f:
        writer=csv.writer(f);writer.writerow(['n','A189281'])
        writer.writerows(LARGE.items())
    report('Numerical errors (signed, for e*a(n)/n! minus truncation):')
    for row in rows: report(str(row))
    report(f'Completed in {time.perf_counter()-start:.2f} seconds.')
    (data/'verification.txt').write_text('\n'.join(lines)+'\n')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order',type=int,default=12)
    args=parser.parse_args()
    if args.order<3:parser.error('--order must be at least 3')
    run(args.order)
