#!/usr/bin/env python3
"""Compute the three prime races modulo 8 in races.tex; uses only Python's standard library."""
import argparse
import csv
import math
import sys


def primes_up_to(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if flags[p]:
            start = p * p
            flags[start::p] = b"\x00" * (1 + (limit - start) // p)
    return [n for n in range(3, limit + 1, 2) if flags[n]]


def races(x, primes):
    log_x = math.log(x)
    sums = {g: [] for g in (1, 3, 5, 7)}
    for p in primes:
        if p > x:
            break
        log_p = math.log(p)
        sums[p % 8].append(log_p * (log_x - log_p) / math.sqrt(p))
    scores = {g: math.fsum(values) for g, values in sums.items()}
    for g in (3, 5, 7):
        difference = scores[g] - scores[1]
        yield (x, g, f"{difference:.8f}", f"{difference / log_x**2:.8f}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("x", type=int, nargs="*", default=[100, 1000, 10000, 100000, 1000000])
    args = parser.parse_args()
    if any(x < 2 for x in args.x):
        parser.error("x must be at least 2")
    primes = primes_up_to(max(args.x))
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(["x", "g", "S_g_minus_S_1", "difference_divided_by_log_x_squared"])
    for x in args.x:
        writer.writerows(races(x, primes))
