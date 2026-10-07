#!/usr/bin/env python3
"""Deterministic exact finite checks. No numerical package is imported in exact mode."""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
MAX_BYTES = 16 * 1024 * 1024
INTEGER_LAWS = ('linear', 'quadratic', 'cubic', 'quartic', 'quintic', 'sextic',
                'quadratic_comparison', 'quartic_comparison', 'quartic_square',
                'quadratic_endpoint', 'cubic_endpoint')
SMALL_LAWS = INTEGER_LAWS + ('critical_rational', 'oscillatory_rational', 'jagged_rational')
FIXTURE_LAWS = ('linear', 'quadratic', 'cubic', 'quartic', 'quadratic_comparison',
                'quartic_comparison', 'oscillatory_rational')


class CheckError(ValueError):
    """Malformed input or failed explicit check (also active under python -O)."""


def require(condition, message):
    if not condition:
        raise CheckError(message)


def canonical_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True,
                       allow_nan=False) + '\n').encode('utf-8')


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def _pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def strict_json(path):
    path = Path(path)
    require(not path.is_symlink() and path.is_file(), 'Expected regular JSON file')
    require(path.stat().st_size <= MAX_BYTES, 'Oversized JSON file')
    try:
        return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=_pairs,
                          parse_constant=lambda value: (_ for _ in ()).throw(CheckError('Nonfinite JSON number')))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise CheckError('Malformed JSON') from exc


def exact_keys(value, keys, label):
    require(type(value) is dict and set(value) == set(keys), 'Malformed ' + label)


def rational_text(value):
    value = Fraction(value)
    return str(value.numerator) if value.denominator == 1 else f'{value.numerator}/{value.denominator}'


def parse_rational(value):
    require(type(value) is str and len(value) < 100000 and
            re.fullmatch(r'-?(0|[1-9][0-9]*)(/[1-9][0-9]*)?', value) is not None,
            'Invalid rational text')
    try:
        out = Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise CheckError('Invalid rational value') from exc
    require(rational_text(out) == value, 'Noncanonical rational')
    return out


def a_term(h):
    return Fraction(1) if h == 0 else 1 + Fraction(1, 3*h) + Fraction((-1)**h, 4*h*h)


def weight(law, h):
    require(type(h) is int and h >= 0, 'Invalid height')
    if h == 0:
        return 0
    powers = {'linear': 1, 'quadratic': 2, 'cubic': 3, 'quartic': 4, 'quintic': 5, 'sextic': 6}
    if law in powers:
        return h**powers[law]
    if law == 'quadratic_comparison': return 4*h*h-1
    if law == 'quartic_comparison': return h*h*(4*h*h-1)
    if law == 'quartic_square': return (h*h+1)**2
    if law == 'quadratic_endpoint': return 2 if h == 1 else h*h
    if law == 'cubic_endpoint': return 2 if h == 1 else h**3
    if law == 'critical_rational': return h*h + Fraction(1, h)
    if law == 'oscillatory_rational': return h**4*a_term(h)/a_term(h-1)
    if law == 'jagged_rational': return Fraction((h*h+3)*(7 if h % 2 else 2), 5)
    raise CheckError('Unknown weight law')


def validate_weights(weights, nmax):
    require(type(nmax) is int and 0 <= nmax <= 1024, 'Invalid maximum degree')
    require(type(weights) in (list, tuple) and len(weights) >= nmax+1, 'Insufficient weights')
    require(type(weights[0]) in (int, Fraction) and weights[0] == 0, 'Height-zero placeholder must be zero')
    for value in weights[1:nmax+1]:
        require(type(value) in (int, Fraction) and value > 0, 'Weights must be exact and positive')


def moments(weights, nmax):
    """Forward transfer with downstep weights, exact integer/rational arithmetic."""
    validate_weights(weights, nmax)
    state = [0]*(nmax+1)
    state[0] = 1
    out = [1]
    for step in range(1, 2*nmax+1):
        nxt = [0]*(nmax+1)
        for h in range(min(step-1, nmax)+1):
            if h < nmax: nxt[h+1] += state[h]
            if h: nxt[h-1] += state[h]*weights[h]
        state = nxt
        if step % 2 == 0: out.append(state[0])
    return out


def determinant(edges):
    older, previous = [1], [1]
    for value in edges:
        current = previous+[0] if len(previous) <= len(older) else previous.copy()
        for j, coefficient in enumerate(older): current[j+1] -= value*coefficient
        older, previous = previous, current
    return previous


def continuant_moments(weights, nmax):
    """Independent path matching polynomial, then formal series division."""
    validate_weights(weights, nmax)
    denominator = determinant(weights[1:nmax+1])
    numerator = determinant(weights[2:nmax+1])
    out = []
    for n in range(nmax+1):
        value = numerator[n] if n < len(numerator) else 0
        value -= sum(denominator[j]*out[n-j] for j in range(1, min(n, len(denominator)-1)+1))
        out.append(value)
    return out


def enumerate_paths(weights, n):
    """Full Dyck enumeration, occupation/hit masses and marked excursions."""
    validate_weights(weights, n)
    z = 0
    occupation, hit, marked = defaultdict(int), defaultdict(int), defaultdict(int)
    def visit(up, down, heights, product, counts):
        nonlocal z
        h = heights[-1]
        if down == n:
            z += product
            for level, count in counts.items():
                occupation[level] += product*count
                if count: hit[level] += product
            for t in range(2*n):
                level = heights[t]
                if heights[t+1] != level-1: continue
                for end in range(t+1, 2*n+1):
                    if heights[end] == level:
                        require((end-t) % 2 == 0, 'Excursion parity')
                        marked[level, (end-t)//2] += product
                        break
            return
        if up < n: visit(up+1, down, heights+[h+1], product, counts)
        if down < up:
            changed = counts.copy()
            changed[h] = changed.get(h, 0)+1
            visit(up, down+1, heights+[h-1], product*weights[h], changed)
    visit(0, 0, [0], 1, {})
    return z, occupation, hit, marked


def primitive_negative(weights, h, k):
    result = 0
    def visit(level, step, product):
        nonlocal result
        if step == 2*k:
            if level == h: result += product
            return
        if level == h and step: return
        if level: visit(level-1, step+1, product*weights[level])
        if step and level < h: visit(level+1, step+1, product)
    visit(h, 0, 1)
    return result


def load_fixtures(path):
    data = strict_json(path)
    exact_keys(data, ('schema', 'scope', 'sequences', 'oscillatory_coefficients'), 'fixture')
    require(data['schema'] == 'report202-exact-fixtures-v1', 'Wrong fixture schema')
    require(data['scope'] == 'Exact finite anchors; not asymptotic evidence', 'Wrong fixture scope')
    seqs = data['sequences']
    require(type(seqs) is list and len(seqs) == len(FIXTURE_LAWS), 'Wrong fixture sequence count')
    require([x.get('law') if type(x) is dict else None for x in seqs] == list(FIXTURE_LAWS), 'Wrong fixture law order')
    for row in seqs:
        exact_keys(row, ('law', 'moments_n0_through_n6'), 'fixture sequence')
        vals = row['moments_n0_through_n6']
        require(type(vals) is list and len(vals) == 7, 'Wrong fixture degree range')
        parsed = [parse_rational(x) for x in vals]
        require(parsed[0] == 1 and all(x > 0 for x in parsed), 'Invalid fixture moments')
        actual = moments([weight(row['law'], h) for h in range(7)], 6)
        require(parsed == actual, 'Fixture arithmetic mismatch')
    exact_keys(data['oscillatory_coefficients'], ('even', 'odd'), 'oscillatory anchors')
    require(data['oscillatory_coefficients'] == {'even': '1/6', 'odd': '-5/6'}, 'Oscillatory anchor mismatch')
    require(Path(path).read_bytes() == canonical_bytes(data), 'Fixture JSON must be canonical')
    return data


def exact_results(nmax=64, fixture_path=None):
    require(type(nmax) is int and 16 <= nmax <= 256, 'Exact maximum must lie in 16..256')
    fixtures = load_fixtures(fixture_path or HERE/'data/fixtures.json')
    counts = defaultdict(int)
    def check(condition, category):
        require(condition, 'Failed exact check: '+category)
        counts[category] += 1
    large = {}
    for law in INTEGER_LAWS:
        weights = [weight(law, h) for h in range(nmax+1)]
        dp, cf = moments(weights, nmax), continuant_moments(weights, nmax)
        for left, right in zip(dp, cf): check(left == right, 'integer_dp_vs_continuant')
        large[law] = [rational_text(x) for x in dp]
    small_data = []
    for law in SMALL_LAWS:
        weights = [weight(law, h) for h in range(9)]
        dp = moments(weights, 8)
        enumerated = [enumerate_paths(weights, n) for n in range(9)]
        @lru_cache(None)
        def excursion(h, k): return primitive_negative(weights, h, k)
        for n, (z, occ, hit, marked) in enumerate(enumerated):
            check(z == dp[n], 'exact_dp_vs_full_enumeration')
            check(sum(occ.values()) == n*z, 'exact_occupation_mass')
            for h in range(1, n+1):
                check(occ[h]-hit[h] == sum(v for (j, k), v in marked.items() if j == h), 'exact_nonlast_descent_count')
                check(excursion(h, 1) == weights[h], 'exact_primitive_k1')
                for cutoff in sorted({0, 1, n//2, n}):
                    lhs = sum(v for (j, k), v in marked.items() if j == h and k > cutoff)
                    rhs = sum(excursion(h, k)*(enumerated[n-k][1][h]+enumerated[n-k][1][h+1])
                              for k in range(max(1, cutoff+1), n-h+1))
                    check(lhs == rhs, 'exact_truncated_excursion_identity')
        z, occ, hit, _ = enumerated[8]
        small_data.append({'law': law, 'n': 8, 'Z': rational_text(z),
                           'occupation_masses': [rational_text(occ[h]) for h in range(1, 9)],
                           'hit_masses': [rational_text(hit[h]) for h in range(1, 9)]})
    # The finite ratio is an exact expectation under the base path measure.
    for changed in ('quadratic_comparison', 'critical_rational', 'oscillatory_rational', 'jagged_rational'):
        base = 'quartic' if changed == 'oscillatory_rational' else 'quadratic'
        wb = [weight(base, h) for h in range(9)]
        wc = [weight(changed, h) for h in range(9)]
        for n in range(9):
            zb = moments(wb, n)[n]
            zc = moments(wc, n)[n]
            ratios = [0]+[Fraction(wc[h], wb[h]) for h in range(1, 9)]
            # Independently enumerate the base product and likelihood ratio.
            value = 0
            def visit(u, d, h, product, likelihood):
                nonlocal value
                if d == n:
                    value += product*likelihood
                    return
                if u < n: visit(u+1, d, h+1, product, likelihood)
                if d < u: visit(u, d+1, h-1, product*wb[h], likelihood*ratios[h])
            visit(0, 0, 0, 1, Fraction(1))
            check(Fraction(value, zb) == Fraction(zc, zb), 'exact_change_of_measure')
    secant = [1]
    for n in range(1, nmax+1):
        secant.append(-sum((-1)**k*comb(2*n, 2*k)*secant[n-k] for k in range(1, n+1)))
    for n in range(nmax+1): check(str(secant[n]) == large['quadratic'][n], 'exact_secant_cosine_convolution')
    poly = [1]
    for k in range(2*min(20, nmax)+1):
        check(poly[0] == (secant[k//2] if k % 2 == 0 else 0), 'exact_secant_operator_constant')
        nxt = [0]*(len(poly)+1)
        for h, value in enumerate(poly):
            if h: nxt[h-1] += h*value
            nxt[h+1] += (h+1)*value
        poly = nxt
    finite_products, product = [], Fraction(1)
    oscillatory, oscillatory_product = [], Fraction(1)
    for n in range(1, 129):
        product *= Fraction(4*n*n-1, 4*n*n)
        rhs = Fraction(factorial(2*n)*factorial(2*n+1), 2**(4*n)*factorial(n)**4)
        check(product == rhs, 'exact_sine_finite_product_factorials')
        oscillatory_product *= a_term(n)/a_term(n-1)
        check(oscillatory_product == a_term(n), 'exact_oscillatory_product_telescope')
        check(a_term(n) > 1, 'exact_oscillatory_positive_anchor')
        if n in (1, 2, 4, 8, 16, 32, 64, 128):
            finite_products.append({'N': n, 'product': rational_text(product)})
            oscillatory.append({'N': n, 'a_N': rational_text(a_term(n)), 'product': rational_text(oscillatory_product)})
    # Formal degree-two log coefficients: log(1+c1*z+c2*z^2) has c2-c1^2/2.
    A, B = Fraction(1, 3), Fraction(1, 4)
    for parity, expected in ((1, Fraction(1, 6)), (-1, Fraction(-5, 6))):
        current = B*parity-A*A/2
        previous = A-B*parity-A*A/2
        check(current-previous == expected, 'exact_oscillatory_log_coefficient')
    for a in (Fraction(-3, 2), Fraction(0), Fraction(7, 3)):
        for c1, c2 in ((Fraction(1), Fraction(2)), (Fraction(-2, 3), Fraction(5, 7))):
            check((c1-a*a/2)-(c2-a*a/2) == c1-c2, 'exact_equal_linear_log_coefficient')
    check(Fraction(1, 24)-2*Fraction(1, 12) == Fraction(-1, 8), 'exact_quadratic_stirling_coefficient')
    for r in (Fraction(1, 10), Fraction(1, 5), Fraction(6, 25)):
        branches = [Fraction(1)]
        for s in range(1, 25):
            value = 2*sum(Fraction(comb(2*k-2, k-1), k)*r**k*branches[s-k] for k in range(1, s+1))
            check(value == comb(2*s, s)*r**s, 'exact_catalan_branch_convolution')
            branches.append(value)
    for row in fixtures['sequences']:
        vals = moments([weight(row['law'], h) for h in range(7)], 6)
        for actual, expected in zip(vals, row['moments_n0_through_n6']):
            check(actual == parse_rational(expected), 'exact_pinned_fixture_identity')
    summary = {'schema': 'report202-exact-checks-v1', 'status': 'PASS', 'max_n': nmax,
               'scope': 'Finite exact identities and positive rational predicates only; no asymptotic proof',
               'counts': dict(sorted(counts.items())), 'total_exact_predicates': sum(counts.values()),
               'fixture_sha256': sha256(canonical_bytes(fixtures))}
    data = {'schema': 'report202-exact-data-v1', 'max_n': nmax, 'integer_moments': large,
            'exact_occupation_at_n8': small_data, 'sine_product_anchors': finite_products,
            'oscillatory_product_anchors': oscillatory,
            'representation': 'Canonical integer/fraction strings; no binary floating point'}
    return {'exact_checks.json': summary, 'exact_data.json': data}


def write_results(out, values):
    out = Path(out)
    require(not out.exists() and not out.is_symlink(), 'Output must be a new directory')
    require(set(values) in ({'exact_checks.json', 'exact_data.json'},
                           {'exact_checks.json', 'exact_data.json', 'numerical_diagnostics.json'}), 'Wrong generated members')
    out.mkdir(parents=True)
    records = []
    for name, value in sorted(values.items()):
        raw = canonical_bytes(value)
        (out/name).write_bytes(raw)
        records.append({'path': name, 'bytes': len(raw), 'sha256': sha256(raw)})
    manifest = {'schema': 'report202-generated-manifest-v1', 'files': records}
    (out/'manifest.json').write_bytes(canonical_bytes(manifest))


def validate_generated(root, verify_diagnostics=False):
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), 'Invalid generated directory')
    actual = list(root.iterdir())
    require(all(x.is_file() and not x.is_symlink() for x in actual), 'Generated tree must contain regular files only')
    names = {x.name for x in actual}
    expected = {'exact_checks.json', 'exact_data.json', 'manifest.json'}
    if 'numerical_diagnostics.json' in names: expected.add('numerical_diagnostics.json')
    require(names == expected, 'Missing or extra generated member')
    manifest = strict_json(root/'manifest.json')
    exact_keys(manifest, ('schema', 'files'), 'generated manifest')
    require(manifest['schema'] == 'report202-generated-manifest-v1', 'Wrong manifest schema')
    records = manifest['files']
    require(type(records) is list and len(records) == len(expected)-1, 'Wrong manifest length')
    require([r.get('path') if type(r) is dict else None for r in records] == sorted(expected-{'manifest.json'}), 'Invalid manifest paths/order')
    for record in records:
        exact_keys(record, ('path', 'bytes', 'sha256'), 'manifest record')
        require(type(record['bytes']) is int and 0 <= record['bytes'] <= MAX_BYTES, 'Invalid byte count')
        require(type(record['sha256']) is str and re.fullmatch('[0-9a-f]{64}', record['sha256']) is not None, 'Invalid digest')
        raw = (root/record['path']).read_bytes()
        require(len(raw) == record['bytes'] and sha256(raw) == record['sha256'], 'Generated checksum mismatch')
        require(raw == canonical_bytes(strict_json(root/record['path'])), 'Noncanonical generated JSON')
    require((root/'manifest.json').read_bytes() == canonical_bytes(manifest), 'Noncanonical manifest')
    summary = strict_json(root/'exact_checks.json')
    require(type(summary) is dict and type(summary.get('max_n')) is int, 'Invalid exact summary')
    regenerated = exact_results(summary['max_n'])
    for name, value in regenerated.items():
        require((root/name).read_bytes() == canonical_bytes(value), 'Generated arithmetic/check inventory mismatch: '+name)
    if 'numerical_diagnostics.json' in names:
        from diagnostics import validate_diagnostics, diagnostic_results
        numeric = strict_json(root/'numerical_diagnostics.json')
        validate_diagnostics(numeric)
        if verify_diagnostics:
            replay = diagnostic_results(numeric['nmax'], numeric['decimal_precision'])
            require(canonical_bytes(replay) == canonical_bytes(numeric), 'Numerical diagnostic replay mismatch')
    return {'status': 'PASS', 'exact_predicates': regenerated['exact_checks.json']['total_exact_predicates'],
            'numerical_replayed': bool(verify_diagnostics and 'numerical_diagnostics.json' in names)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--out', type=Path, help='new output directory, never overwritten')
    group.add_argument('--verify', type=Path, help='validate hashes AND recompute all exact data')
    parser.add_argument('--max-n', type=int, default=64)
    parser.add_argument('--diagnostics', action='store_true', help='generate/replay mpmath diagnostics separately')
    parser.add_argument('--diagnostic-nmax', type=int, default=256)
    args = parser.parse_args()
    if args.verify:
        result = validate_generated(args.verify, verify_diagnostics=args.diagnostics)
    else:
        values = exact_results(args.max_n)
        if args.diagnostics:
            from diagnostics import diagnostic_results
            values['numerical_diagnostics.json'] = diagnostic_results(args.diagnostic_nmax, 90)
        write_results(args.out, values)
        result = {'status': 'PASS', 'exact_predicates': values['exact_checks.json']['total_exact_predicates'],
                  'numeric_predicates': values.get('numerical_diagnostics.json', {}).get('numerical_predicate_total', 0)}
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
