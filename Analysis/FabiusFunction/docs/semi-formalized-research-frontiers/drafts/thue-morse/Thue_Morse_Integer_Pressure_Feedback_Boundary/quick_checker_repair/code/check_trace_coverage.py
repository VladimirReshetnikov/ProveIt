from repair_common import require, options, VerificationError
"""Independent standard-library validation of every saved parity trace.

This validates baseline vectors, all scalar error recurrences, dimensions,
final interval arithmetic, and exact/full-vector cross-comparisons. The
matrix inverses and per-coordinate rounding are certified in the audited
generator by exact identities and inequalities.
"""
from pathlib import Path
from math import comb, factorial, gcd
from functools import reduce
from fractions import Fraction as Q
import gzip, json, sys, hashlib
sys.set_int_max_str_digits(0)
ARGS = options('Verify all 68 saved traces, failing on incomplete or corrupt data')
BASE = ARGS.data_dir / 'certificates'

def read_trace(path):
    opener = gzip.open if path.suffix == '.gz' else open
    with opener(path, 'rt') as f:
        header = f.readline().split()
        scale = int(f.readline())
        even = tuple(map(int, f.readline().split()))
        odd = tuple(map(int, f.readline().split()))
        rows = [list(map(int, line.split())) for line in f]
    return (header, scale, even, odd, rows)

def audit(m):
    p = BASE / f'parity_m{m:03d}.json'
    tp = Path(str(p) + '.trace.gz')
    if not tp.exists():
        tp = Path(str(p) + '.trace')
    if not p.exists() or not tp.exists():
        return None
    z = json.loads(p.read_text())
    head, S, ev, od, rows = read_trace(tp)
    d = 2 * m
    D = 2 ** (d - 1)
    require(head == ['TMP1', str(m), str(d), '256'], "Failed exact check: head == ['TMP1', str(m), str(d), '256']")
    require(z['m'] == m and z['precision_bits'] == 256 and (z['checked_response_orders'] == d), "Failed exact check: z['m'] == m and z['precision_bits'] == 256 and (z['checked_response_orders'] == d)")
    require(len(rows) == d + 1, 'Failed exact check: len(rows) == d + 1')
    require(all((len(row) == m + 1 - n % 2 for n, row in enumerate(rows))), 'Failed exact check: all((len(row) == m + 1 - n % 2 for n, row in enumerate(rows)))')
    e = [1]
    for r in range(2, d):
        e = [(k + 1) * (e[k] if k < len(e) else 0) + (r - k) * (e[k - 1] if k else 0) for k in range(r)]
    den = factorial(d - 1)
    g = reduce(gcd, e, den)
    e = [v // g for v in e]
    den //= g
    require(S == 2 ** 256 * den ** 2 == int(z['common_denominator']), "Failed exact check: S == 2 ** 256 * den ** 2 == int(z['common_denominator'])")
    require(rows[0][:-1] == [e[m - 1 + k] * (S // den) for k in range(m)], 'Failed exact check: rows[0][:-1] == [e[m - 1 + k] * (S // den) for k in range(m)]')
    require(rows[0][-1] == 0, 'Failed exact check: rows[0][-1] == 0')
    errors = [row[-1] for row in rows]
    for n in range(1, d + 1):
        alpha, q = ev if n % 2 == 0 else od
        require(alpha >= 0 and q > 0, 'Failed exact check: alpha >= 0 and q > 0')
        bound = alpha * D * sum((comb(d, j) * errors[n - j] for j in range(1, n + 1)))
        round_cost = d - 1 if n % 2 == 0 else d - 2
        require(errors[n] == (bound + q - 1) // q + round_cost, 'Failed exact check: errors[n] == (bound + q - 1) // q + round_cost')
    v = rows[-1][:-1]
    mid = (v[0] + 2 * sum(((-1) ** k * v[k] for k in range(1, m)))) * (-1) ** m
    require(mid - errors[-1] == int(z['H_lower_numerator']) > 0, "Failed exact check: mid - errors[-1] == int(z['H_lower_numerator']) > 0")
    require(mid + errors[-1] == int(z['H_upper_numerator']), "Failed exact check: mid + errors[-1] == int(z['H_upper_numerator'])")
    require(errors[-1] == int(z['error_radius_numerator']), "Failed exact check: errors[-1] == int(z['error_radius_numerator'])")
    lo, hi = (Q(mid - errors[-1], S), Q(mid + errors[-1], S))
    exact = False
    full = False
    ep = BASE / f'gmp_m{m:03d}.json'
    if not ep.exists():
        ep = BASE / f'm{m:03d}.json'
    if ep.exists():
        ex = json.loads(ep.read_text())
        v = Q(ex['H_boundary_numerator']) / Q(ex['H_boundary_denominator'])
        require(lo <= v <= hi, 'Failed exact check: lo <= v <= hi')
        exact = True
    fp = BASE / f'fixed_m{m:03d}.json'
    if fp.exists():
        old = json.loads(fp.read_text())
        l = Q(old['H_lower_numerator']) / Q(old['common_denominator'])
        u = Q(old['H_upper_numerator']) / Q(old['common_denominator'])
        require(max(lo, l) <= min(hi, u), 'Failed exact check: max(lo, l) <= min(hi, u)')
        full = True
    return {'m': m, 'orders': d, 'exact_rational_comparison': exact, 'full_vector_comparison': full, 'positive_margin_bits': mid.bit_length() - errors[-1].bit_length(), 'json_sha256': hashlib.sha256(p.read_bytes()).hexdigest(), 'trace_sha256': hashlib.sha256(tp.read_bytes()).hexdigest()}
def main():
    out = {'range': [2, 69], 'certified_moments': 0, 'checked_response_orders': 0,
           'missing': [], 'records': [], 'complete': False}
    try:
        manifest = json.loads((Path(__file__).resolve().parents[1] / 'input_manifest.json').read_text())
        missing = []
        corrupt = []
        for rel, expected in manifest['certificate_sha256'].items():
            path = ARGS.data_dir / rel
            if not path.is_file():
                missing.append(rel)
            elif hashlib.sha256(path.read_bytes()).hexdigest() != expected:
                corrupt.append(rel)
        out['missing_files'] = missing
        out['corrupt_files'] = corrupt
        require(not missing, 'Incomplete certificate dataset: ' + ', '.join(missing))
        require(not corrupt, 'Certificate SHA256 mismatch: ' + ', '.join(corrupt))
        for m in range(2, 70):
            r = audit(m)
            require(r is not None, f'Missing JSON or trace for m={m}')
            out['records'].append(r)
        out['certified_moments'] = len(out['records'])
        out['checked_response_orders'] = sum(r['orders'] for r in out['records'])
        require(out['certified_moments'] == 68, 'Expected all 68 moment traces')
        require(out['checked_response_orders'] == 4828, 'Expected 4828 response orders')
        out['complete'] = True
    except Exception as exc:
        out['error'] = f'{type(exc).__name__}: {exc}'
        (ARGS.output_dir / 'trace_checks.json').write_text(json.dumps(out, indent=2) + '\n')
        print(out['error'], file=sys.stderr)
        return 1
    (ARGS.output_dir / 'trace_checks.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Verified all 68 moment traces and 4828 response orders; manifest integrity passed')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
