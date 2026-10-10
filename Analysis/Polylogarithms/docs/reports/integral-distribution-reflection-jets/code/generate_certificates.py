#!/usr/bin/env python3
"""Generate the three frozen polynomial identities used in the article."""
from pathlib import Path
import json
from distribution import Distribution

ROOT = Path(__file__).resolve().parents[1]

def main():
    records = []
    for q, a in [(12, 1), (15, 8), (30, 1)]:
        d = Distribution(q)
        records.append({
            'level': q, 'point_index': a, 'prime_order': list(d.primes),
            'basis_indices': list(d.basis),
            'normal_form': [{'point': b, 'polynomial': c.encode()}
                            for b, c in sorted(d.normal_form(a).items())],
            'row_combination': [{'prime': p, 'target': x, 'polynomial': c.encode()}
                                for (p, x), c in sorted(d.certificate(a).items())],
            'selected_unit_minor_size': d.check_unit_minor(),
        })
    obj = {'schema': 'weighted-distribution-certificate-v1',
           'meaning': 'e_point - normal_form = sum coefficient * raw_prime_row',
           'polynomial_format': '[[exponent_vector, integer_coefficient], ...]',
           'records': records}
    path = ROOT / 'data' / 'identity_certificates.json'
    path.write_text(json.dumps(obj, indent=2) + '\n')
    print(f'Wrote {len(records)} certificates to {path.name}')

if __name__ == '__main__':
    main()
