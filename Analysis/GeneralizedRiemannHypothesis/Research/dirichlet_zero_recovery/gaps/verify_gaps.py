#!/usr/bin/env python3
"""Reproduce the spacing table in gaps.tex with the Python standard library."""
import argparse
from itertools import combinations
from math import ceil, floor, fsum, log, prod, tau


def elementary(weights, k):
    return fsum(prod(group) for group in combinations(weights, k))


def tail(weights, x):
    if x >= 1 / max(weights):
        return 0.0
    return fsum(w * prod(1 - z * x for j, z in enumerate(weights) if j != i)
                for i, w in enumerate(weights))


def observe(primes, phases, height, sample_points):
    """Collect complete gaps between positive zeros below height."""
    rates = [log(p) / tau for p in primes]
    intensity = fsum(rates)
    events = []
    for i, (rate, phase) in enumerate(zip(rates, phases)):
        start = floor(-phase) + 1
        end = ceil(rate * height - phase)
        for n in range(start, end):
            events.append(((n + phase) / rate, i))
    events.sort()
    gap_count = len(events) - 1
    if gap_count <= 0:
        raise ValueError("increase the sample height")
    gaps = [intensity * (right[0] - left[0]) for left, right in zip(events, events[1:])]
    largest = max(range(len(primes)), key=lambda i: primes[i])
    same_largest = sum(a[1] == b[1] == largest for a, b in zip(events, events[1:]))
    frequencies = [sum(g > x for g in gaps) / gap_count for x in sample_points]
    return gap_count, frequencies, same_largest / gap_count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=float, default=1_000_000)
    args = parser.parse_args()
    if args.height <= 0:
        parser.error("--height must be positive")
    primes = [2, 3, 5]
    log_product = log(prod(primes))
    weights = [log(p) / log_product for p in primes]
    points = [0.25, 0.75, 1.25, 1.75, 2.0]
    cutoff = 1 / max(weights)
    atom = max(weights) * prod(1 - w * cutoff for w in weights if w < max(weights))
    e2 = elementary(weights, 2)
    e3 = elementary(weights, 3)
    for x in points:
        assert abs(tail(weights, x) - (1 - 2 * e2 * x + 3 * e3 * x ** 2)) < 1e-14
    print("weights:    ", *(f"{w:.10f}" for w in weights))
    print(f"cutoff:      {cutoff:.10f}   mass at cutoff: {atom:.10f}")
    print(f"tail polynomial: 1 - {2 * e2:.10f} x + {3 * e3:.10f} x^2")
    print(f"height: {args.height:g}")
    samples = [observe(primes, phases, args.height, points)
               for phases in ([0, 0, 0], [0, 0.5, 0.5])]
    print(f"complete gaps counted: {samples[0][0]} (mod 30), {samples[1][0]} (mod 210)")
    print("x                  limit        mod 30       mod 210")
    for i, x in enumerate(points):
        print(f"{x:.2f}       {tail(weights, x):12.8f}  "
              f"{samples[0][1][i]:12.8f}  {samples[1][1][i]:12.8f}")
    print(f"endpoint mass {atom:11.8f}  {samples[0][2]:12.8f}  {samples[1][2]:12.8f}")


if __name__ == "__main__":
    main()
