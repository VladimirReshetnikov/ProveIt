#!/usr/bin/env python3
"""Run exact finite checks; these supplement, not replace, the article proofs."""
from __future__ import annotations
import itertools
import json
from fractions import Fraction as F
from pathlib import Path
from spectral_core import (Root, ONE, increasing_core, positive_admissible,
    realizable, difference_spectrum, fixed_point_realizable,
    fixed_point_free_realizable, affine_rigid)

OUT = Path(__file__).resolve().parents[1] / 'results'

def polynomial_product(a: list[F], b: list[F]) -> list[F]:
    out = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out

def determinant(a: list[list[F]]) -> F:
    b = [row[:] for row in a]
    d = F(1)
    for i in range(len(b)):
        p = next((j for j in range(i,len(b)) if b[j][i]), None)
        if p is None:
            return F(0)
        if p != i:
            b[i], b[p] = b[p], b[i]
            d = -d
        pivot = b[i][i]
        d *= pivot
        for j in range(i+1,len(b)):
            q = b[j][i]/pivot
            for k in range(i+1,len(b)):
                b[j][k] -= q*b[i][k]
    return d

def spectrum(groups, exponents):
    return {r:m for rs,m in zip(groups,exponents) for r in rs if m}

def audit_grid(groups, max_m):
    patterns = list(itertools.product(range(max_m+1), repeat=len(groups)))
    good = {e:realizable(spectrum(groups,e)) for e in patterns}
    checks = 0
    for e in patterns:
        expected = [0]*len(groups)
        for d in itertools.product(*(range(m+1) for m in e)):
            checks += 1
            if good[d]:
                expected = [max(a,b) for a,b in zip(expected,d)]
        original = spectrum(groups,e)
        got = increasing_core(original)
        assert got == spectrum(groups,expected), (e, expected, got)
        assert increasing_core(got) == got
        assert all(got.get(r,0) <= m for r,m in original.items())
        if got:
            assert realizable(got)
        assert realizable(original) == (bool(original) and got == original)
    return {'spectra':len(patterns), 'divisors_checked':checks}

def orbit_certificate(name, fn, factors):
    coeff = [F(1)]
    for factor in factors:
        coeff = polynomial_product(coeff, list(map(F,factor)))
    degree = len(coeff)-1
    for n in range(-80,81):
        assert sum((a*fn(n+j) for j,a in enumerate(coeff)), F(0)) == 0
    matrix = [[fn(i+j) for j in range(degree)] for i in range(degree)]
    det = determinant(matrix)
    assert det != 0
    return {'name':name,'degree':degree,'coefficients_ascending':list(map(str,coeff)),
        'initial_values':[str(fn(n)) for n in range(2*degree)],
        'hankel_matrix':[[str(a) for a in row] for row in matrix],
        'hankel_determinant':str(det), 'recurrence_n_range':[-80,80]}

def main():
    half, two, negtwo = Root(F(1,2)), Root(2), Root(-2)
    ii, iii = Root(0,1), Root(0,3)
    grids = [audit_grid([(half,), (ONE,), (two,), (negtwo,),
                         (ii,ii.conjugate()), (iii,iii.conjugate())], 2),
             audit_grid([(ONE,), (two,), (negtwo,), (ii,ii.conjugate())], 4)]
    u = lambda n: F(2)**n*(4-n) + F(4)**n*(F(n,3)+F(2,9))
    v = lambda n: F(2)**n*(2-n) + F(4)**n*(2+n)
    sin = lambda n: (0,1,0,-1)[n%4]
    a = lambda n: F(2)**n - F(2)**(-n) + F(sin(n),10)
    for n in range(-100,101):
        assert u(n+1)-u(n) == v(n) > 0
        assert a(n+1)>a(n)
    certs = [orbit_certificate('even endpoint multiplicities',u,
                [[-2,1],[-2,1],[-4,1],[-4,1]]),
             orbit_certificate('analytic annular nonreal example',a,
                [[F(-1,2),1],[-2,1],[1,0,1]])]
    assert increasing_core({ONE:1,two:2}) == {ONE:1,two:1}
    assert not realizable({ONE:1,two:2})
    assert not affine_rigid({ONE:1,two:1})
    assert affine_rigid({ONE:3})
    annular = {half:1,two:1,ii:3,ii.conjugate():3}
    assert realizable(annular) and fixed_point_free_realizable(annular)
    assert not fixed_point_realizable(annular)
    assert fixed_point_realizable({half:1,two:1})
    assert fixed_point_free_realizable({half:1,two:1})
    assert not fixed_point_realizable({half:1,two:2})
    assert fixed_point_free_realizable({half:1,two:2})
    example = {ONE:3,half:2,two:4,negtwo:7,
               ii:5,ii.conjugate():5,iii:3,iii.conjugate():3}
    expected = {ONE:3,half:2,two:4,negtwo:4,ii:5,ii.conjugate():5}
    assert increasing_core(example)==expected
    data = {'status':'PASS','arithmetic':'exact rational',
        'finite_scope_warning':'The grids check formula consistency, not the universal mathematical proof.',
        'core_grids':grids,'orbit_certificates':certs,
        'annular_example_degree_reduction':[sum(example.values()),sum(expected.values())]}
    OUT.mkdir(exist_ok=True)
    (OUT/'exact_checks.json').write_text(json.dumps(data,indent=2)+'\n')
    lines = ['All exact checks passed.',
        f"Core grids: {sum(g['spectra'] for g in grids)} spectra; "
        f"{sum(g['divisors_checked'] for g in grids)} divisors checked.",
        'Two recurrence windows: -80 <= n <= 80.',
        '402 exact monotonicity / increment assertions over -100 <= n <= 100 (two sequences).']
    for c in certs:
        lines.append(f"{c['name']}: degree {c['degree']}, Hankel determinant {c['hankel_determinant']}.")
    lines.append('Degree-reduction example: 32 -> 23.')
    text = '\n'.join(lines)+'\n'
    (OUT/'verification.txt').write_text(text)
    print(text,end='')

if __name__ == '__main__':
    main()
