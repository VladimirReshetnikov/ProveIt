from repair_common import require, options, VerificationError
ARGS = options('Exact analytical certificate; repaired acceptance checks')
"""Exact elementary inequalities for the analytic m>=70 cutoff."""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json

def sqrt_bounds(x, scale=10 ** 16):
    n = isqrt(x.numerator * scale ** 2 // x.denominator)
    return (F(n, scale), F(n + 1, scale))
bs = []
lo = hi = F(1)
for j in range(1, 13):
    bs.append((lo, hi))
    _, u = sqrt_bounds(1 + lo * lo)
    l, _ = sqrt_bounds(1 + hi * hi)
    lo, hi = (lo / (1 + u), hi / (1 + l))
for lo, hi in bs:
    require(lo <= hi, 'Failed exact check: lo <= hi')
atlo = F(4, 5)
athi = F(5, 6)
mean_upper = sum((atlo * hi / (1 + atlo * hi) for lo, hi in bs)) + atlo * F(2) ** (1 - len(bs))
mean_lower = sum((athi * lo / (1 + athi * lo) for lo, hi in bs))
require(mean_upper < 1 < mean_lower, 'Failed exact check: mean_upper < 1 < mean_lower')
require(F(143, 100) ** 2 > 2, 'Failed exact check: F(143, 100) ** 2 > 2')
require(F(10, 7) ** 2 > 2, 'Failed exact check: F(10, 7) ** 2 > 2')
require(F(10) * (4 + 3 * F(10, 7)) / 8 < 11, 'Failed exact check: F(10) * (4 + 3 * F(10, 7)) / 8 < 11')
q = F(206, 225)
d = 140
require((1 + F(81, 100) * atlo) / (1 + atlo) == q, 'Failed exact check: (1 + F(81, 100) * atlo) / (1 + atlo) == q')
threshold = (F(275, 36) * 16) ** 2 * (d + 2) ** 2 * d * q ** (2 * d)
require(threshold < 1, 'Failed exact check: threshold < 1')
ratio = F(143, 142) * F(281, 280) * q
require(ratio < 1, 'Failed exact check: ratio < 1')
require(2 ** d > 32 * d, 'Failed exact check: 2 ** d > 32 * d')
out = {'all_checks_passed': True, 'cutoff_m': 70, 'tangent_intervals': [[str(a), str(b)] for a, b in bs], 'saddle_mean_at_4_over_5_upper': str(mean_upper), 'saddle_mean_at_5_over_6_lower': str(mean_lower), 'tail_factor_bound': str(q), 'threshold_squared': str(threshold), 'successive_bound_ratio': str(ratio)}
(ARGS.output_dir / 'cutoff_certificate.json').write_text(json.dumps(out, indent=2) + '\n')
print('Exact cutoff inequalities pass; saddle is between4/5 and5/6; m>=70 suffices')
