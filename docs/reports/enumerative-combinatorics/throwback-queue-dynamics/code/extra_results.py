"""Check the extremal-period theorem and generate exact examples."""
from __future__ import annotations
import csv
import json
from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb, gcd
from pathlib import Path
from throwback import maximum_core_period, first_obstruction, certified_orbit, sorted_statistics

OUT = Path(__file__).resolve().parents[1] / 'data'
OUT.mkdir(exist_ok=True)

def brute_maximum(r):
    best, best_path, count = 0, None, 0
    def walk(a, p, left, path):
        nonlocal best, best_path, count
        if left == 0:
            count += 1
            if p > best:
                best, best_path = p, path
            return
        for b in range(2, a + 2):
            walk(b, b * p // gcd(p, b - 1), left - 1, path + (b,))
    walk(1, 1, r - 1, (1,))
    return best, best_path, count

records = []
for r in range(2, 14):
    actual, path, count = brute_maximum(r)
    expected, k = maximum_core_period(r)
    assert actual == expected
    assert count == comb(2 * r - 2, r - 1) // r
    s = tuple([i + q - 1 for i, q in enumerate(reversed(path))])
    stats = sorted_statistics(s, closed=True)
    assert stats['period'] == expected
    records.append(dict(r=r, critical_multisets=count, maximum_period=actual,
                        maximizing_k=k, maximizing_weights=' '.join(map(str,s))))
with (OUT / 'extremal_periods.csv').open('w', newline='') as f:
    w = csv.DictWriter(f, fieldnames=records[0].keys())
    w.writeheader(); w.writerows(records)

examples = []
for weights in [[2, 100, 2, 1, 1], [1, 2, 3, 1], [2, 2, 2, 1, 1],
                [1, 1, 2, 2, 2], [3, 3, 4, 4, 4], [3, 4, 3, 4, 4]]:
    cert = first_obstruction(weights)
    assert cert is not None and cert.verify()
    orbit = certified_orbit(cert)
    stats = sorted_statistics(cert.core_weights, closed=True)
    assert orbit['labeled_period'] == stats['period']
    examples.append(dict(input=weights, first_bad_index=cert.first_bad_index,
                         threshold=cert.threshold, core_labels=cert.core_labels,
                         core_weights=cert.core_weights, orbit=orbit,
                         frequencies=[str(x) for x in stats['frequencies']]))
(OUT / 'examples.json').write_text(json.dumps(examples, indent=2) + '\n')

# The product's omitted tail satisfies prod_{k>N}(1-2^-k) >= 1-2^-N.
N = 160
upper = Fraction(1)
for k in range(1, N + 1):
    upper *= 1 - Fraction(1, 2 ** k)
lower = upper * (1 - Fraction(1, 2 ** N))
with localcontext() as ctx:
    ctx.prec = 65
    data = dict(factors=N,
                lower_decimal=str(Decimal(lower.numerator)/Decimal(lower.denominator)),
                upper_decimal=str(Decimal(upper.numerator)/Decimal(upper.denominator)),
                error_upper_decimal=str(Decimal(1)/Decimal(2**N)),
                bound='R_N*(1-2^(-N)) <= R_infinity <= R_N')
(OUT / 'escape_product_bounds.json').write_text(json.dumps(data, indent=2) + '\n')
print(json.dumps({'extremal_profiles_checked': sum(x['critical_multisets'] for x in records),
                  'largest_r': records[-1]['r'], 'examples':len(examples),
                  'escape_product':data}, indent=2))
