#!/usr/bin/env python3
"""Build the two rigorously proved polynomial-majorant nine-variable tails.

The V8 certificate is the primary polynomial in a cancellation-resolved form.
The major2048 certificate is D**16 times the primary polynomial.  D is a
nonzero polynomial, so its degree and leading coefficient are subtracted
exactly when deriving the primary degree; the equation itself has no division.
"""
from pathlib import Path
from collections import Counter
import json
import build as source_builder
from common import DAG, ROOT
import nine_refined
import nine_majorant

VARIANTS = {
    'v8': (nine_refined, 964, 240, 0, 1, 1730),
    'major2048': (nine_majorant, 820, 208, 16, 3, 1494),
}
PRIMES = (1000003, 1000033, 1000000007)


def build(mode, layout, variant, certificate=False):
    tail, slope, offset, multiplier, lead_factor, lead_exp = VARIANTS[variant]
    d = DAG()
    v, b, B, N, R, Y, cap, meta, data = source_builder.source(d, mode, layout)
    out = tail.finish(d, v, b, B, N, R, cap, certificate)
    nodes, out, names = d.export(out)
    counts = Counter(n['kind'] for n in nodes if 'left' in n)
    meta.update(
        schema='support-aware-refined-nine-v2',
        variant=variant,
        domain='positive integers' if mode == 'nine_positive' else 'nonnegative integers',
        nodes=nodes, output=out, named_nodes=names,
        operation_counts=dict(counts), total_operations=sum(counts.values()),
        certificate_form=certificate,
        certificate_multiplier={'register': 'D', 'exponent': multiplier} if certificate else None,
    )
    return meta, data


def main():
    dest = ROOT / 'refined'
    dest.mkdir(exist_ok=True)
    results = []
    for variant, (_, slope, offset, multiplier, factor, lead_exp) in VARIANTS.items():
        for layout in ('uniform', 'overlap'):
            for mode in ('nine_positive', 'nine_natural'):
                body, data = build(mode, layout, variant)
                cert, _ = build(mode, layout, variant, True)
                receipts = [source_builder.degree_bound_certificate(cert, data, p) for p in PRIMES]
                W = body['W']
                t = 3 * (body['targets'][-1] + 3 * W + 2)
                degree = slope * t + 12 * W + offset
                multiplier_degree = multiplier * (20 * t + 4)
                expected_cert_degree = degree + multiplier_degree
                for r in receipts:
                    if r['propagated_bound'] != expected_cert_degree:
                        raise ValueError('Unexpected certificate degree')
                    if r['coefficient_at_bound'] != factor * pow(2, lead_exp + 34 * multiplier, r['prime']) % r['prime']:
                        raise ValueError('Nonzero leading coefficient differs from exact formula')
                leading = f'{factor}*2^{lead_exp}' if factor != 1 else f'2^{lead_exp}'
                body.update(exact_degree=degree, diagonal_leading_coefficient=leading,
                            degree_certificate=receipts, certificate_multiplier_degree=multiplier_degree)
                cert.update(certifies_primary_degree=degree, multiplier_degree=multiplier_degree)
                for suffix, doc in (('', body), ('_degree_certificate', cert)):
                    (dest / f'{layout}_{mode}_{variant}{suffix}.json').write_text(
                        json.dumps(doc, separators=(',', ':')) + '\n')
                results.append(dict(variant=variant, layout=layout, domain=mode,
                                    operations=body['total_operations'], exact_degree=degree,
                                    W=W, Hmax=body['targets'][-1], t=t,
                                    diagonal_leading_coefficient=leading))
    (dest / 'metrics.json').write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
