"""The exact periodic mask does not repair deletion of the main-index block.

Symbolic 28-operation source checks and finite exact outer counterexamples.
The enormous positive Pell extension is proved in the companion note.
"""

from collections import Counter
import json
from pathlib import Path
import sympy as sp

import round37_1980_binary_product_certificate as published
from explore_fixed_radix_pell_kernel import evaluate


def verify():
    full = [row for row in published.SCHEDULE[33:77] if row[0] != 'R13']
    reduced = [row for row in published.SCHEDULE[33:63]
               if row[0] not in {'R13', 'tr1'}]
    assert len(full) == 43 and len(reduced) == 28
    counts = Counter(row[1] for row in reduced)
    assert counts == {'*': 16, '+': 12}
    computed = {row[0] for row in reduced}
    inputs = {v for row in reduced for v in row[2:]
              if isinstance(v, str) and v not in computed}
    inputs |= {'a', 'c', 'd', 'k'}
    symbols = {name: sp.Symbol(name) for name in inputs}
    env = evaluate(reduced, symbols)
    U, Y = symbols['w']*symbols['n2'], symbols['s']*symbols['n2']
    a,c,d,k,tau = [symbols[name] for name in ('a','c','d','k','tau')]
    residuals = [
        U*Y**2*(U*Y**2+1)*k**2-tau*(tau+1),
        c-Y*k-symbols['eta'],
        k-symbols['eta']-symbols['zeta'],
        k-symbols['r']-1-symbols['h']*U*Y,
        a-Y*(U+1),
        d-U-a*c-symbols['ga']*(4*a+3),
        d*d-(a*a+4*a+3)*c*c-1,
    ]
    equalities = [('L9','R9'), ('c','R10a'), ('k','R10b'),
                  ('k','R11'), ('a','R12'), ('d','R14'), ('L15','R15')]
    records = []
    for (left,right), expected in zip(equalities, residuals):
        actual = sp.expand(env[left]-env[right])
        assert sp.expand(actual-expected) == 0
        records.append({'equality':[left,right], 'residual':sp.sstr(actual)})

    cases = []
    for z in range(1, 62, 3):
        q = 1 << z
        Q = q*q
        Q2, Q4 = Q*Q, Q**4
        L, D0, N0 = Q4*Q4, Q**12, Q**6
        assert D0 == L*Q4 and Q4 == Q2*Q2
        Pcode = 8
        lam, rem = divmod(L-1,3)
        assert rem == 0 and lam > 0
        r = (L-Pcode)*(L-1)+2*lam
        assert 0 < Pcode < Q**6
        assert N0*N0 < r < Q**16 < N0**3
        assert r % 2 == 0 and r % 3 == 1 and L % 9 == 7
        h, rem = divmod(r-1,3)
        assert rem == 0 and h >= 2 and h % 2 == 1
        p,t,J = 6*h+1,3*h+2,2*r+1
        assert p == J-2 and t == r+1 and p >= r+2
        assert 4*h > 24*z and p > 24*z
        assert D0*D0 > J and D0*D0 > r+1
        M = 2*lam
        assert Pcode+M < L
        carry_count = Pcode.bit_count()+M.bit_count()-(Pcode+M).bit_count()
        assert carry_count == 1
        assert r.bit_count() == 24*z-1
        assert D0 == 1 << (24*z)
        assert Pcode % 4 == 0 and ((Pcode//4) % 4) == 2
        cases.append({'z':z, 'q':q, 'r':r, 'h':h, 'main_index':p,
                      'intended_index':J, 'first_index':t,
                      'popcount_r':r.bit_count(), 'required_valuation':24*z,
                      'positive_scaling_exponents_verified':True})
    return {
        'status':'AUXILIARY_DELETION_REFUTED_FOR_SPECIALIZED_BOOLEAN_COMPONENT',
        'symbolic_arithmetic_status':'PASS',
        'original_kernel_operations':43,
        'auxiliary_deleted_operations':28,
        'histogram':dict(counts),
        'special_outer_operations':11,
        'invalid_component_pair_operations':39,
        'schedule':reduced,
        'equality_residuals':records,
        'outer_counterexample_cases':cases,
        'case_count':len(cases),
        'scope':'Exact seven-source residuals and specialized outer counterexamples; huge Pell coordinates are not materialized. Their positive extension is proved in the note. No surrounding machine transition/input conditions are asserted.',
        'proof':'../1980/EXPLORATION_PERIODIC_MASK_AUXILIARY_DELETION.md',
    }


if __name__ == '__main__':
    receipt = verify()
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(receipt['status'])
    print('28 operations;', receipt['case_count'],
          'exact outer cases; seven symbolic residuals PASS')
