#!/usr/bin/env python3
"""Pinned supplementary checks for complete74_negative_index_refinement.

No historical imports, whole zero search, maintained compiler, or inverse claim.
The parametric proof is in the companion note; finite checks only corroborate it.
"""
import argparse
import hashlib
import json
from pathlib import Path

PINS = {
    'complete74_nonlinear_index_projection_scout.py': '610739f1074ad792e8010287e8e162d509832c8d5e7444dc38ecae98e7710c71',
    'complete74_nonlinear_index_projection_scout.json': 'ea982f9585eb4e16d756dfc33c73041e73e5e18a38ea37c2302d57c1fe104c92',
    'complete74_nonlinear_index_projection_scout.md': '2034e1343f9c4c059525445c6ef1ae287dec48c0da9d9d27123f1e5745c2c40d',
    'review_complete74_nonlinear_index_bootstrap.py': 'e231aec5c761db3cc553c49cac5e33269755c8f5acaf6bfa905f5d63d166582f',
    'review_complete74_nonlinear_index_bootstrap.json': '851d3900efd066e73df54da846d7c2a2211eaf1cd8deb82a0647b4bec354e7c5',
    'review_complete74_nonlinear_index_bootstrap.md': '4922eb2587fa1ecda313792ea0644c6da123b5ebdb86a0dbdfa02671d48ed1a8',
    'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992',
    '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md': 'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d',
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def exact(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def authenticate(root):
    blobs = {}
    for name, pin in PINS.items():
        data = (root / name).read_bytes()
        if digest(data) != pin:
            raise ValueError('Dependency byte mismatch: ' + name)
        blobs[name] = data
    return blobs


def pell(A, n, modulus=None):
    """Independently exponentiate A+sqrt(A*A-1), optionally modulo m."""
    assert type(A) is int and A >= 2 and type(n) is int and n >= 0
    D = A*A - 1
    def mul(left, right):
        x, y = left
        z, w = right
        result = (x*z + D*y*w, x*w + y*z)
        return tuple(v % modulus for v in result) if modulus else result
    out, factor = (1, 0), (A, 1)
    while n:
        if n & 1:
            out = mul(out, factor)
        factor = mul(factor, factor)
        n //= 2
    return out


def actual_interfaces(blob):
    forms = json.loads(blob)['forms']
    assert [f['packet']['mode'] for f in forms] == ['raw30', 'positive22', 'signed20']
    result = []
    for form in forms:
        p = form['packet']
        rows = {r[0]: r[1:] for r in p['source']}
        assert len(rows) == 74
        mode = p['mode']
        k = 'k' if mode == 'raw30' else 'R10b'
        a = 'a' if mode == 'raw30' else 'R12'
        c = 'c' if mode == 'raw30' else 'R10a'
        kap = 'kappa' if mode == 'raw30' else 'index_rhs'
        expected = {
            'Lbig': ['*', 'q', 'q'], 'n2': ['*', 'Lbig', 'q'],
            'wn2': ['*', 'w', 'n2'], 'sn2': ['*', 's', 'n2'],
            'UM': ['*', 'wn2', 'sn2'], 'R12': ['+', 'UM', 'sn2'],
            'ksn2': ['*', k, 'sn2'],
            'R10a': ['+', 'ksn2', 'eta'], 'R10b': ['+', 'eta', 'zeta'],
            'hpm1': ['*', 'h', 'UM'], 'index_partial': ['-', k, 'hpm1'],
            'restored_r': ['-', 'index_partial', 1],
            'first_root_base': ['*', 'UM', 'ksn2'],
            'first_next': ['+', 'first_root_base', k],
            'L9': ['*', 'first_root_base', 'first_next'],
            'tau_square': ['*', 'tau', 'tau'], 'R9': ['-', 'tau_square', 1],
            'cam2': ['*', c, a], 'D1': ['+', 'wn2', 'cam2'],
            'a4': ['*', 4, a], 'a4m5': ['+', 'a4', 3],
            'a_square': ['*', a, a], 'A': ['+', 'a_square', 'a4m5'],
            'odd_index': ['+', 'scaled_t', 'inner_bits'],
            'scaled_t': ['*', 'twice_cell_bits', 'x'],
            'index_product': ['*', 'delta', 'A'],
            'index_rhs': ['+', 'odd_index', 'index_product'],
            'kappa2': ['*', kap, kap], 'scaled_kappa2': ['*', 'A', 'kappa2'],
            'norm_rhs': ['+', 'scaled_kappa2', 1],
            'difference_multiple': ['*', kap, a],
            'modulus_multiple': ['*', 'rho', 'a4m5'],
            'exponent_partial': ['+', 'W', 'difference_multiple'],
            'exponent_rhs': ['+', 'exponent_partial', 'modulus_multiple'],
        }
        for name, row in expected.items():
            assert rows[name] == row, (mode, name)
        assert ['L9', 'R9'] in p['comparisons']
        assert ['L15', 'R15'] in p['comparisons']
        assert ['mu2', 'norm_rhs'] in p['comparisons']
        if mode != 'signed20':
            assert 'W' in p['witnesses'] and 'phi' in p['witnesses']
            assert rows['pell_gap'] == ['+', kap, 'phi']
            assert [c, 'pell_gap'] in p['comparisons']
            assert ['raw_bound', 'q'] in p['comparisons']
            assert rows['marked_rhs'] == ['+', 'Z', 'W']
        else:
            assert 'W' not in p['witnesses'] and 'phi' not in p['witnesses']
            assert 'pell_gap' not in rows
        if mode == 'raw30':
            assert ['a', 'R12'] in p['comparisons']
            assert ['c', 'R10a'] in p['comparisons']
            assert ['k', 'R10b'] in p['comparisons']
            assert ['d', 'R14'] in p['comparisons']
            assert ['kappa', 'index_rhs'] in p['comparisons']
            assert ['mu', 'exponent_rhs'] in p['comparisons']
            assert ['C', 'marked_rhs'] in p['comparisons']
        result.append({'mode': mode, 'premise_rows_checked': len(expected),
                       'positive_input_gap_retained': mode != 'signed20',
                       'new_refinement_scope': mode != 'signed20'})
    return result


def verify(root):
    blobs = authenticate(root)
    interfaces = actual_interfaces(blobs['complete74_nonlinear_index_projection_scout.json'])
    counts = dict(discriminant_recurrences=0, input_window_cases=0,
                  first_main_ratio_bounds=0, growth_jump_pairs=0,
                  exponent_exclusion_integer_bounds=0)
    # Direct integer recurrence, independently compared with binary Pell powers.
    for A in (2, 4, 6, 18, 66):
        prev, cur = 0, 1
        for e in range(1, 33):
            assert cur == pell(A, e)[1]
            assert cur % (A*A-1) == (e if e % 2 else e*A) % (A*A-1)
            prev, cur = cur, 2*A*cur-prev
            counts['discriminant_recurrences'] += 1
    windows = []
    for q in (16, 32, 64, 256):
        for w, s in ((1, 1), (2, 1), (1, 2)):
            X, Y = w*q**3, s*q**3
            E, a = X*Y, Y*(X+1)
            A, D = a+2, (a+2)**2-1
            for u in (9, q-1, 2*q-1):
                assert 0 < u < 2*q and u % 2 == 1
                assert (q+1)*E < (q+1)*A < D
                assert u*A < D and A % 2 == 0
                for e in (u, u*A):
                    assert pell(A, e, D)[1] == u
                windows.append([q, w, s, u, A, D])
                counts['input_window_cases'] += 1
    # Fixed small inequality fixtures; these are not full-system zero candidates.
    for X, Y in ((4, 3), (8, 5), (16, 16), (64, 17), (4096, 4096)):
        a = Y*(X+1)
        A, P = a+2, 2*X*Y*Y+1
        assert 3*X*Y*Y > a
        for n in range(2, 9):
            for p in range(n+1, 2*n, 2):
                if p % 2 == 0:
                    continue
                d = 2*n-p
                c, k = pell(A, p)[1], 2*pell(P, n)[1]
                assert c > (2*A-1)**(p-1)
                assert k <= 2*(2*P)**(n-1)
                assert c*(2**d)*Y**(d-1)*X**(n-1) > k*(X+1)**(p-1)
                if c < k*(Y+1):
                    assert a**d * 2**d * (Y+1) > X**n * Y
                    assert a**d * 3**d > X**n
                counts['first_main_ratio_bounds'] += 1
    for A, P, Y in ((5, 17, 2), (20, 101, 8), (100, 1001, 16)):
        for p in (3, 7, 13, 17):
            for n in (2, 4, 9, 13):
                c, cp = pell(A, p)[1], pell(A, p+2)[1]
                k, km = 2*pell(P, n)[1], 2*pell(P, n-1)[1]
                assert cp*k > (2*A-1)**2 * c*km
                assert Y*(2*A-1)**2 > Y+1
                counts['growth_jump_pairs'] += 1
    for q in (16, 32, 64):
        for w in (1, 2):
            X = w*q**3
            for d in (1, 3, 5):
                for p in (13, 17, 25):
                    assert X >= 4**d and X > 9
                    # The lower bound for a^(2d) exceeds (2^p)^(2d).
                    assert X**(p+d) > 3**(2*d) * 2**(2*d*p)
                    assert 2**p > 3*p
                    counts['exponent_exclusion_integer_bounds'] += 1
    q, X, Y, u = 16, 16**3, 16**3, 9
    A = Y*(X+1)+2
    coarse_boundary = {'q': q, 'X': X, 'Y': Y, 'u': u, 'A': A,
                       'odd_input_index': u, 'even_input_index': u*A,
                       'main_index_upper': (q+1)*X*Y,
                       'scope': 'input residue windows only; not a full zero or valid compiler instance'}
    assert u*A < coarse_boundary['main_index_upper']
    return {'schema': 'complete74-negative-index-refinement-v1',
            'source_sha256': digest(Path(__file__).read_bytes()),
            'dependency_pins': dict(PINS), 'actual_interfaces': interfaces,
            'counts': counts,
            'input_window_digest': digest(json.dumps(windows, separators=(',', ':')).encode()),
            'coarse_even_input_boundary': coarse_boundary,
            'theorems': {
                'domain': 'positive integer zeros, raw30 or positive22, valid fixed complete75 compiler slices',
                'input_indices': ['u', 'u*A'],
                'negative_defect': 'd=2*n-p is odd and 4^d>X>=q^3; hence d>=7',
                'representative_uniqueness': 'at most one main index p for each fixed q,X,Y,v',
                'representatives': '1<=v<=3*q+2; 2*p+6<=v*X*Y<=3*p-3',
                'signed20_included': False,
                'positive_inverse_resolved': False,
                'full_counterexample_materialized': False,
                'new_arithmetic_or_universal_bound': False,
                'finite_checks_replace_proofs': False}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = verify(args.root.resolve())
    encoded = json.dumps(result, sort_keys=True, indent=2) + '\n'
    assert exact(result, json.loads(encoded))
    if args.expect is not None:
        assert exact(result, json.loads(args.expect.read_text())), 'Receipt mismatch'
    if args.output is not None:
        args.output.write_text(encoded)
    print(json.dumps({'status': 'PASS', 'counts': result['counts']}, sort_keys=True))


if __name__ == '__main__':
    main()
