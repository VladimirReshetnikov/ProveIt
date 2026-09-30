#!/usr/bin/env python3
"""Reference weighted-support sampler using the transversal-matroid basis walk.

Python 3.10+, standard library only. Each output uses a fresh, independent walk
from the private-copy basis. The conservative burn-in follows the cited ALOV
mixing bound, not an empirical convergence diagnostic. Outputs are support sets,
NOT integer demand vectors. See article.tex for the mathematical hypotheses.

Example:
  python code/support_sampler.py --rows 14,3,5,9 --receivers 4 --samples 100 \
      --epsilon 1/100 --seed 20260929 --output results/sampler_smoke.json

Element weights are exact positive rationals, e.g. --weights 1,2,3/2,5.
The receiver-support law is proportional to count(S) * product(weights[y],y in S).
The optional error parameter bounds total variation for the entire independent
sample batch, under the ideal independent-random-bit model.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from math import lcm
from pathlib import Path
import json
import random
import secrets
import time

from verify import independent_ground


def validate(rows: tuple[int, ...], receivers: int,
             weights: tuple[Fraction, ...]) -> None:
    if receivers < 0 or any(row < 0 or row >> receivers for row in rows):
        raise ValueError('Rows must be nonnegative bit masks within the receiver set.')
    if len(weights) != receivers or any(w <= 0 for w in weights):
        raise ValueError('Exactly one positive rational weight per receiver is required.')


def ceil_log2(x: Fraction) -> int:
    """A conservative nonnegative integer k with 2**k >= x."""
    if x <= 1:
        return 0
    k = max(0, x.numerator.bit_length() - x.denominator.bit_length())
    while Fraction(1 << k) < x:
        k += 1
    return k


def integer_categorical(weights: list[Fraction], rng) -> int:
    """Exact categorical sampling using integer rejection inside randrange."""
    denominator = lcm(*(w.denominator for w in weights))
    counts = [w.numerator * (denominator // w.denominator) for w in weights]
    draw = rng.randrange(sum(counts))
    for i, count in enumerate(counts):
        if draw < count:
            return i
        draw -= count
    raise RuntimeError('Unreachable categorical-sampling state.')


def sample_supports(rows: tuple[int, ...], receivers: int, samples: int,
                    epsilon: Fraction = Fraction(1, 100),
                    weights: tuple[Fraction, ...] | None = None,
                    seed: int | None = None) -> dict:
    """Return support masks and a conservative reproducible mixing certificate.

    With a seed, a deterministic pseudorandom generator is used for reproducible
    experiments. The theorem's randomness guarantee assumes independent uniform
    random bits; a finite-seed run is not an independent proof of that guarantee.
    """
    if samples < 0 or not 0 < epsilon < 1:
        raise ValueError('samples must be nonnegative and 0 < epsilon < 1.')
    if weights is None:
        weights = (Fraction(1),) * receivers
    validate(rows, receivers, weights)
    m, n = len(rows), receivers
    ground_weights = (Fraction(1),) * m + weights
    b = max((max(w.numerator.bit_length(), w.denominator.bit_length())
             for w in ground_weights if w != 1), default=0)
    k = ceil_log2(Fraction(max(samples, 1), 1) / epsilon)
    # log(2) < 1: d*(N + 2*d*b + k + 2) dominates
    # d*log(1/(eta*pi(B0))) for eta=epsilon/max(samples,1).
    steps = m * (m + n + 2*m*b + k + 2)
    rng = secrets.SystemRandom() if seed is None else random.Random(seed)
    outputs: list[int] = []
    start = time.monotonic()
    for _ in range(samples):
        basis = tuple(range(m))
        for _step in range(steps):
            removed = rng.randrange(m)
            retained = basis[:removed] + basis[removed+1:]
            retained_set = set(retained)
            candidates = [f for f in range(m+n) if f not in retained_set and
                          independent_ground(rows, n, retained + (f,))]
            if not candidates:
                raise RuntimeError('A basis deletion must have an extension.')
            index = integer_categorical([ground_weights[f] for f in candidates], rng)
            basis = tuple(sorted(retained + (candidates[index],)))
        outputs.append(sum(1 << (e-m) for e in basis if e >= m))
    histogram = Counter(outputs)
    return {
        'rows': rows, 'receivers': receivers, 'samples': samples,
        'weights': [str(w) for w in weights],
        'batch_total_variation_bound': str(epsilon),
        'basis_rank': m, 'ground_elements': m+n,
        'weight_exponent_bound': b, 'burn_in_steps_per_sample': steps,
        'seed': seed,
        'randomness': 'SystemRandom' if seed is None else 'seeded pseudorandom experiment',
        'support_masks': outputs,
        'support_histogram': {str(k): v for k,v in sorted(histogram.items())},
        'elapsed_seconds': round(time.monotonic()-start, 4),
        'boundary': 'Outputs are supports, not integer vectors. No full FPRAS is implemented.'
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--rows', required=True, help='Comma-separated donor-neighborhood masks.')
    parser.add_argument('--receivers', type=int, required=True)
    parser.add_argument('--samples', type=int, default=100)
    parser.add_argument('--epsilon', type=Fraction, default=Fraction(1,100))
    parser.add_argument('--weights', help='Comma-separated positive rational receiver weights.')
    parser.add_argument('--seed', type=int, default=None)
    parser.add_argument('--output', type=Path, default=Path('results/support_samples.json'))
    args = parser.parse_args()
    try:
        rows = tuple(int(s.strip(), 0) for s in args.rows.split(',') if s.strip())
        weights = (tuple(Fraction(s.strip()) for s in args.weights.split(','))
                   if args.weights is not None else None)
        result = sample_supports(rows, args.receivers, args.samples,
                                 args.epsilon, weights, args.seed)
    except (ValueError, ZeroDivisionError) as exc:
        parser.error(str(exc))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k != 'support_masks'}, indent=2))


if __name__ == '__main__':
    main()
