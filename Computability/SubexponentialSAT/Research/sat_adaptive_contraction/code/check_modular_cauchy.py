#!/usr/bin/env python3
"""Independent finite checks of finite-precision joint Cauchy tables."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import random

from modular_cauchy import ModularCauchy, Ring, reconstruct
from reference_joint_cauchy import JointCauchyKernel, Quadratic, exact_divide, residue
from reference_recurrence import feature_tables as recurrence_tables


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('validation.json'))
    args = parser.parse_args()
    counts = Counter()
    signatures = []

    def check(condition, label):
        if not condition:
            raise ArithmeticError(label)
        counts[label] += 1

    zetas = ((0, 0), (1, 0), (-2, 0), (0, 1), (1, 1), (2, 2))
    for a in range(1, 5):
        for i in range(a):
            for t in sorted({-(1 << i), 1 << i,
                             *((3 << i,) if (3 << i) < (1 << a) else ())}):
                for zeta in zetas:
                    z = (Fraction(zeta[0]) if zeta[1] == 0 else Quadratic(*zeta))
                    exact = JointCauchyKernel(a, i, t, z)
                    target, source = exact.feature_tables()
                    n = exact.size
                    # Independent original polynomial entry: cancel the specific
                    # divisor before forming the product, not the factorization.
                    direct = []
                    for row in range(n):
                        direct_row = []
                        for col in range(n):
                            omitted = exact.slot(col)-exact.slot(row)
                            numerator = Fraction(1)
                            denominator = 1
                            for q in range(-exact.L, exact.L):
                                if q != omitted:
                                    numerator *= exact.T-q
                                if q:
                                    denominator *= -q
                            direct_row.append(exact_divide(numerator, denominator))
                        direct.append(direct_row)
                    for p in (1, 2, 4, 7, 11, 19, 32):
                        fast = ModularCauchy(a, i, t, zeta, p)
                        ft, fs = fast.feature_tables()
                        rt, rs = recurrence_tables(exact, p)
                        check(len(ft) == len(rt), 'safe_mode_count')
                        for b in range(fast.B):
                            for j in range(n):
                                check(ft[b][j] == residue(target[b][j], p), 'exact_target_match')
                                check(fs[b][j] == residue(source[b][j], p), 'exact_source_match')
                                check(ft[b][j] == residue(rt[b][j], p), 'recurrence_target_match')
                                check(fs[b][j] == residue(rs[b][j], p), 'recurrence_source_match')
                        for row in range(n):
                            for col in range(n):
                                check(reconstruct(ft, fs, row, col, fast.ring) == residue(direct[row][col], p),
                                      'independent_polynomial_reconstruction')
                        nonbatch = ModularCauchy(a, i, t, zeta, p, batch_inverses=False)
                        check(nonbatch.feature_tables() == (ft, fs), 'batch_inverse_equivalence')
                        stream = ModularCauchy(a, i, t, zeta, p)
                        for j, tc, sc in stream.iter_columns():
                            check(tc == [ft[b][j] for b in range(stream.B)]
                                  and sc == [fs[b][j] for b in range(stream.B)],
                                  'stream_matches_tables')
                        signatures.append(hashlib.sha256(repr((a, i, t, zeta, p, ft, fs)).encode()).hexdigest())

    rng = random.Random(20261026)
    for p in (1, 2, 7, 32, 65, 128):
        ring = Ring(p)
        xs = []
        for _ in range(100):
            x = (rng.randrange(ring.mod), rng.randrange(ring.mod))
            if not ((x[0] | x[1]) & 1):
                x = (x[0] | 1, x[1])
            xs.append(x)
        inverse = ring.batch_inverse(xs)
        for x, y in zip(xs, inverse):
            check(ring.mul(x, y) == (1, 0), 'random_batch_units')

    bad = [lambda: Ring(0), lambda: Ring(4).inv((2, 2)),
           lambda: Ring(4).batch_inverse([(1, 0), (2, 2)]),
           lambda: ModularCauchy(0, 0, 1, (1, 0), 4),
           lambda: ModularCauchy(3, 3, 1, (1, 0), 4),
           lambda: ModularCauchy(3, 1, 1, (1, 0), 4),
           lambda: ModularCauchy(3, 0, 0, (1, 0), 4),
           lambda: ModularCauchy(3, 0, 1, (Fraction(1, 2), 0), 4)]
    for fn in bad:
        try:
            fn()
        except (ValueError, TypeError):
            counts['invalid_input_rejected'] += 1
        else:
            raise ArithmeticError('invalid input accepted')
    result = {'status':'PASS', 'optimized_python':not __debug__, 'counts':dict(counts),
              'cases':len(signatures),
              'canonical_digest':hashlib.sha256(('\n'.join(signatures)+'\n').encode()).hexdigest(),
              'scope':'Exact local tables and polynomial reconstruction only; not an end-to-end SAT solver.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
