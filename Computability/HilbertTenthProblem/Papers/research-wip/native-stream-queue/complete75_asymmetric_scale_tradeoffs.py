"""Keep Y=s*q^3 and lower X's paid scale to q in complete87/88.

The unchanged operation totals have exact degrees169/125.  The proof
restores the parent positive integer w after decoding the main power;
off-zero source replay uses an explicitly rational coordinate map.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import complete75_normalized_strong87 as normalized_parent
import complete75_coupled_index_linear88 as ordinary_parent

RETAINED = normalized_parent.RETAINED
FACTOR_NAMES = normalized_parent.FACTOR_NAMES
FACTOR_DEGREES = {
    True: (12, 18, 32, 56, 7, 3, 34, 7),
    False: (12, 18, 32, 24, 7, 3, 22, 7),
}


def parent(normalized=True):
    assert type(normalized) is bool
    return normalized_parent if normalized else ordinary_parent


def rewrite(old, normalized=True):
    """Only the complete selected frozen polynomial is a supported caller."""
    expected = parent(normalized).sources()[3]
    assert old == expected, 'not the selected complete canonical parent'
    rows = {n: (op, a, b) for n, op, a, b in old}
    assert rows['wn2'] == ('*', 'w', 'n2')
    assert rows['sn2'] == ('*', 's', 'n2')
    assert rows['n2'] == ('*', 'Lbig', 'q')
    new = [(n, op, a, 'q' if n == 'wn2' else b)
           for n, op, a, b in old]
    assert {n for n, op, a, b in new if (op, a, b) != rows[n]} == {'wn2'}
    return new


def source(normalized=True):
    return rewrite(parent(normalized).sources()[3], normalized)


def run(rows, values, fixed):
    return normalized_parent.eliminated.run(
        rows, normalized_parent.eliminated.fixed_inputs({**values, **fixed}))


def to_parent(values, B):
    """Exact rational off-zero map; integral and positive at positive zeros."""
    q = (B-1)*values['Jrep']+1
    assert q != 0
    return {**values, 'w': Fraction(values['w'], q*q)}


def from_parent(values, B):
    q = (B-1)*values['Jrep']+1
    return {**values, 'w': values['w']*q*q}


def ledger(normalized=True):
    rows = source(normalized)
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in rows)
    expected = dict(M=48, A=39) if normalized else dict(M=47, A=41)
    assert count == expected
    return dict(operations=len(rows), multiplications=count['M'],
                additions_subtractions=count['A'], certificate_operations=len(rows)-1,
                equations=1, positive_witnesses=len(RETAINED),
                exact_degree=sum(FACTOR_DEGREES[normalized]),
                factor_degrees=FACTOR_DEGREES[normalized])


def closure(rows):
    free = set(RETAINED+normalized_parent.eliminated.baseline.prior.CONSTANTS+
               ['x', 'Bm1', 'Kconstant', 'twice_cell_bits'])
    available = set(free)
    for n, op, a, b in rows:
        assert n not in available and op in ('+', '-', '*')
        assert all(type(v) is int or v in available for v in (a, b))
        available.add(n)
    nodes = {n: (op, a, b) for n, op, a, b in rows}
    pending, live = ['polynomial'], set()
    while pending:
        n = pending.pop()
        if type(n) is int or n in free or n in live:
            continue
        live.add(n)
        pending.extend(nodes[n][1:])
    assert live == set(nodes)
    return len(live)


def source_audit():
    rng = random.Random(87169125)
    records = []
    for normalized in (True, False):
        old = parent(normalized).sources()[3]
        rows = source(normalized)
        closure(rows)
        counts = Counter()
        for case in range(384):
            signed = case >= 192
            values = {n: rng.randrange(-7, 8) if signed else rng.randrange(1, 8)
                      for n in RETAINED+['x']}
            B = (16, 32, 128, 256)[case % 4]
            fixed = dict(B=B, DC=3, DR=5, MC=B-2, MF=4,
                         cell_bits=B.bit_length()-1, inner_bits=3)
            current = run(rows, values, fixed)
            lifted = run(old, to_parent(values, B), fixed)
            assert all(current[n] == lifted[n] for n, *_ in rows)
            assert from_parent(to_parent(values, B), B) == values
            image = from_parent(values, B)
            projected = run(rows, image, fixed)
            original = run(old, values, fixed)
            assert all(projected[n] == original[n] for n, *_ in rows)
            assert to_parent(image, B) == values
            if not signed:
                assert all(v > 0 for v in image.values())
            q = current['q']
            assert current['wn2'] == values['w']*q
            assert current['sn2'] == values['s']*q**3
            counts['whole_register_output_identities'] += 2
            counts['signed_assignment_identities'] += 2*int(signed)
            counts['nonintegral_offzero_inverse'] += to_parent(values, B)['w'].denominator != 1
        bad = [old[:-1], old+[('unused', '+', 1, 1)]]
        changed = list(old)
        i = next(i for i, row in enumerate(changed) if row[0] == 'sn2')
        changed[i] = ('sn2', '*', 's', 'q')
        bad.append(changed)
        bad.append(parent(not normalized).sources()[3])
        for candidate in bad:
            try:
                rewrite(candidate, normalized)
            except AssertionError:
                pass
            else:
                raise AssertionError('noncanonical caller accepted')
        records.append(dict(normalized=normalized, ledger=ledger(normalized),
                            source=rows, output='polynomial', comparison=['eight_units', 1],
                            every_gate_live=True,
                            source_sha256=hashlib.sha256(json.dumps(rows).encode()).hexdigest(),
                            rejection_cases=len(bad), **counts))
    return records


def degree_audit():
    z = sp.Symbol('z')
    records = []
    for normalized in (True, False):
        for B, offset in ((16, 0), (64, 1), (256, 2)):
            scales = {n: 1+(i+offset) % 4 for i, n in enumerate(RETAINED+['x'])}
            scales.update(tau_gap=5, eta=1, zeta=2, Jrep=2, x=1)
            values = {n: sp.Poly(scales[n]*z+i+1, z)
                      for i, n in enumerate(RETAINED+['x'])}
            fixed = dict(B=B, DC=3, DR=5, MC=B-2, MF=4,
                         cell_bits=B.bit_length()-1, inner_bits=3)
            env = run(source(normalized), values, fixed)
            factors = [env[n] for n in FACTOR_NAMES]
            assert tuple(p.degree() for p in factors) == FACTOR_DEGREES[normalized]
            Q = (B-1)*scales['Jrep']
            k = scales['eta']+scales['zeta']
            C = Q-scales['F']-scales['Z']-scales['alpha']-2*fixed['cell_bits']*scales['x']
            common = (32*scales['h']**2*(scales['rho']+scales['sigma'])*
                      scales['delta']**2*C*(2*scales['tau_gap']-k))
            top = (common*Q**101*scales['i']**4*k**12*scales['w']**17*scales['s']**28
                   if normalized else
                   -common*Q**73*scales['i']**2*scales['f']**2*k**8*
                   scales['w']**13*scales['s']**20)
            assert top != 0
            assert env['polynomial'].degree() == sum(FACTOR_DEGREES[normalized])
            assert env['polynomial'].LC() == top
            records.append(dict(normalized=normalized, B=B, scales=scales,
                                factor_degrees=FACTOR_DEGREES[normalized],
                                exact_degree=env['polynomial'].degree(),
                                leading_coefficient=str(top)))
    return records


def range_audit():
    counts = Counter()
    for q in (16, 17, 31, 32, 64, 257):
        for w in (1, 2, 7):
            for s in (1, 3):
                X, Y = w*q, s*q**3
                E, A, P = X*Y, Y*(X+1)+2, 2*X*Y*Y+1
                assert P > A and E >= q**4
                lo, hi = (2*q-1)*(q*q-1), q**4-q**3
                for R in (lo+1, lo+2, (lo+hi)//2, hi-2, hi-1):
                    for epsilon in (-1, 1):
                        assert 0 < R+epsilon < E and E > R+q**3
                        k = R+epsilon+E
                        assert k*Y > 2*(R+2)
                        for lam in (-1, 1):
                            p = R+epsilon-lam
                            assert R-2 <= p <= R+2
                            for wrap in (-2, -1, 0, 1, 2):
                                n2 = R+epsilon+wrap*E
                                if 0 < n2 < 2*p:
                                    assert wrap == 0
                                counts['first_index_wrap_cases'] += 1
                        counts['pretyping_cases'] += 1
    for X in (16, 17, 32, 64, 256):
        for r in range(1, 65):
            # This exact inequality is the only power-size bound used
            # after the lower ratio.  It assumes no upper ratio error.
            assert X**r >= 6
            assert 3*2**(2*r+1) < X**(r+1)
            counts['lower_ratio_no_wrap_bounds'] += 1
    for t in range(4, 129):
        q = 1 << t
        p = (2*q-1)*(q*q-1)-1
        assert p > 3*t
        counts['restored_scale_divisibility_bounds'] += 1
    return dict(counts)


def pell_audit():
    pell = normalized_parent.pell
    recurrence_cases = 0
    for A in range(3, 35):
        a, H = A-2, 4*A-5
        for n in range(1, 33):
            D, c = pell(A, n)
            assert (D-a*c-pow(2, n, H)) % H == 0
            recurrence_cases += 1
    # Main/first component fixtures only: these do not assert the full
    # outer compiler, the scale divisibility, or giant auxiliary zeros.
    records = []
    for p in (3, 7, 11, 15, 19):
        r = (p-1)//2
        X = 1 << p
        M = sum(int(sp.binomial(2*r, r+j))*X**j for j in range(r+1))
        assert M % 2 == 0
        Y = M//2
        a, E, P = Y*(X+1), X*Y, 2*X*Y*Y+1
        A, H = a+2, 4*a+3
        D, c = pell(A, p)
        tau, half_k = pell(P, r+1)
        k = 2*half_k
        eta, zeta = c-k*Y, k-(c-k*Y)
        g = tau-E*Y*k
        assert min(eta, zeta, g) > 0
        assert (k-p-1) % E == 0 and (k-p-1)//E > 0
        assert (D-a*c-X) % H == 0 and (D-a*c-X)//H > 0
        assert g*g+E*k*Y*(2*g-k) == 1
        assert D*D-(A*A-1)*c*c == 1
        xi = Fraction((X+1)**(2*r), X**r)
        assert xi/2 < Fraction(c, k) < Y+1
        records.append(dict(p=p, X=X, Y_bits=Y.bit_length(),
                            c_bits=c.bit_length(), ratio_slacks_positive=True,
                            first_main_and_projection_identities=True,
                            full_compiler_zero=False))
    return dict(main_projection_recurrence_cases=recurrence_cases,
                half_binomial_main_first_components=records)


def verify():
    return dict(status='PASS_COMPLETE75_ASYMMETRIC_SCALE_TRADEOFFS',
                source=source_audit(), degree=degree_audit(),
                pretyping=range_audit(), pell_components=pell_audit(),
                coordinate_maps=dict(old_to_new='w_new=q^2*w_old; other coordinates unchanged',
                                     new_to_old='w_old=w_new/q^2; positive integral on positive zeros',
                                     offzero='Exact complete polynomial/register identity over rationals for q!=0'),
                scope='For each selected frozen87/88 parent, a bijection of full positive integer zero sets under the unchanged actual fixed compiler contract. Same operation and witness counts; exact degrees169/125. No reduced operation bound or complete numerical universal Pell tuple is asserted.')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert result == json.loads(path.read_text()), 'receipt mismatch'
    print(result['status'])
    print([record['ledger'] for record in result['source']])


if __name__ == '__main__':
    main()
