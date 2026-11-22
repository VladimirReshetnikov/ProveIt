#!/usr/bin/env python3
"""Exact dyadic interval certificates for finite Robin inequalities.

All acceptance decisions use Python integers. No floating-point operation,
external numerical library, or unbounded precision-search loop is used.
The mathematical soundness proof is in paper/report.tex. This executable
is not an iPRA proof checker and is not a proof of Robin's equivalence.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from dataclasses import dataclass
from pathlib import Path


def ceil_div(a: int, b: int) -> int:
    assert b > 0
    return -((-a) // b)


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    def __post_init__(self):
        assert self.lo <= self.hi


class ExactIntervals:
    def __init__(self, bits: int = 72, terms: int = 32, gamma_m: int = 2048):
        assert bits >= 8 and terms >= 2 and gamma_m >= 2
        self.bits, self.terms, self.gamma_m = bits, terms, gamma_m
        self.S = 1 << bits
        self.log2 = self._atanh_log(2, 1)
        self.gamma = self._gamma_interval()
        assert 0 <= self.gamma.lo <= self.gamma.hi <= self.S
        self.exp_gamma = self.exp01(self.gamma)

    def _atanh_log(self, a: int, b: int) -> Interval:
        """Enclose log(a/b), assuming 1 <= a/b <= 2."""
        assert 0 < b <= a <= 2 * b
        S, K = self.S, self.terms
        zl = S * (a-b) // (a+b)
        zu = ceil_div(S * (a-b), a+b)
        z2l = zl * zl // S
        z2u = ceil_div(zu * zu, S)
        pl, pu, low, high = zl, zu, 0, 0
        for j in range(K):
            low += 2 * pl // (2*j + 1)
            high += ceil_div(2 * pu, 2*j + 1)
            pl = pl * z2l // S
            pu = ceil_div(pu * z2u, S)
        # Since z <= 1/3, the omitted tail is at most
        # 2*z^(2K+1)/((2K+1)*(1-z^2)) <= 9/(4*(2K+1)*3^(2K+1)).
        high += ceil_div(9 * S, 4 * (2*K + 1) * 3**(2*K + 1))
        return Interval(low, high)

    def log_ratio(self, a: int, b: int = 1) -> Interval:
        assert a > 0 and b > 0
        if a < b:
            v = self.log_ratio(b, a)
            return Interval(-v.hi, -v.lo)
        # a/b >= 1. The loop is bounded by bit_length(a)+1.
        exponent = max(0, a.bit_length() - b.bit_length())
        scaled_b = b << exponent
        if scaled_b > a:
            exponent -= 1
            scaled_b >>= 1
        assert scaled_b <= a < 2 * scaled_b
        small = self._atanh_log(a, scaled_b)
        return Interval(exponent * self.log2.lo + small.lo,
                        exponent * self.log2.hi + small.hi)

    def _gamma_interval(self) -> Interval:
        S, m = self.S, self.gamma_m
        hl = sum(S // j for j in range(1, m+1))
        hu = sum(ceil_div(S, j) for j in range(1, m+1))
        lg = self.log_ratio(m)
        # H_m-log(m)-1/(2m) <= gamma <= that expression+1/(12m^2).
        return Interval(hl-lg.hi-ceil_div(S, 2*m),
                        hu-lg.lo-S//(2*m)+ceil_div(S, 12*m*m))

    def exp01(self, v: Interval) -> Interval:
        assert 0 <= v.lo <= v.hi <= self.S
        S, K = self.S, self.terms
        tl = tu = low = high = S
        for j in range(1, K+1):
            tl = tl * v.lo // (S*j)
            tu = ceil_div(tu * v.hi, S*j)
            low += tl
            high += tu
        high += ceil_div(2*S, math.factorial(K+1))
        return Interval(low, high)

    def mul(self, a: Interval, b: Interval) -> Interval:
        products = (a.lo*b.lo, a.lo*b.hi, a.hi*b.lo, a.hi*b.hi)
        return Interval(min(products)//self.S,
                        ceil_div(max(products), self.S))

    def robin_bound(self, n: int) -> Interval:
        """Enclose B(n)=exp(gamma)*log(log(n)), for n>=2."""
        assert n >= 2
        lg = self.log_ratio(n)
        assert lg.lo > 0
        ll_lo = self.log_ratio(lg.lo, self.S)
        ll_hi = self.log_ratio(lg.hi, self.S)
        return self.mul(self.exp_gamma, Interval(ll_lo.lo, ll_hi.hi))


def sigma_sieve(limit: int) -> list[int]:
    assert limit >= 2
    sigma = [0] * (limit+1)
    for d in range(1, limit+1):
        for n in range(d, limit+1, d):
            sigma[n] += d
    return sigma


EXPECTED_EXCEPTIONS = [2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20,
                       24, 30, 36, 48, 60, 72, 84, 120, 180, 240,
                       360, 720, 840, 2520, 5040]


def audit(limit: int, output_dir: Path, bits: int = 72,
          terms: int = 32, gamma_m: int = 2048) -> dict:
    assert limit >= 5041
    output_dir.mkdir(parents=True, exist_ok=True)
    iv = ExactIntervals(bits, terms, gamma_m)
    sigma = sigma_sieve(limit)
    failures, unknown = [], []
    minimum = None
    min_n = None
    csv_path = output_dir / 'finite_robin_certificates.csv'
    with csv_path.open('w', newline='') as stream:
        writer = csv.writer(stream)
        writer.writerow(['n', 'sigma', 'bound_lo_numerator',
                         'bound_hi_numerator', 'scale_power_of_two', 'sign'])
        for n in range(2, limit+1):
            bound = iv.robin_bound(n)
            positive_margin = n*bound.lo - sigma[n]*iv.S
            negative_margin = sigma[n]*iv.S - n*bound.hi
            if positive_margin > 0:
                sign = 'holds'
                # Compare certified B(n)-sigma(n)/n lower bounds exactly.
                if n >= 5041 and (minimum is None or
                    positive_margin*min_n < minimum*n):
                    minimum, min_n = positive_margin, n
            elif negative_margin > 0:
                sign = 'fails'
                failures.append(n)
            else:
                sign = 'undetermined'
                unknown.append(n)
            writer.writerow([n, sigma[n], bound.lo, bound.hi, bits, sign])
    assert not unknown, unknown
    assert failures == EXPECTED_EXCEPTIONS, failures
    boundary = iv.robin_bound(5041)
    assert 4*boundary.lo > 15*iv.S  # Infinite family with <=3 prime factors.
    result = {
        'scope': 'finite interval only; not Robin equivalence or RH',
        'limit_inclusive': limit, 'integers_checked': limit-1,
        'bits': bits, 'log_and_exp_terms': terms, 'gamma_m': gamma_m,
        'exp_gamma_interval': {'lo': iv.exp_gamma.lo, 'hi': iv.exp_gamma.hi,
                               'denominator': iv.S},
        'gamma_interval': {'lo': iv.gamma.lo, 'hi': iv.gamma.hi,
                           'denominator': iv.S},
        'failures': failures, 'undetermined': unknown,
        'smallest_certified_positive_margin_above_5040': {
            'n': min_n, 'numerator': minimum, 'denominator': min_n*iv.S},
        'bound_5041_interval': {'lo': boundary.lo, 'hi': boundary.hi,
                               'denominator': iv.S},
        'bound_5041_gt_15_over_4': 4*boundary.lo > 15*iv.S,
        'csv_sha256': hashlib.sha256(csv_path.read_bytes()).hexdigest(),
    }
    (output_dir/'summary.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


def verify_csv(path: Path, recompute_intervals: bool = True) -> dict:
    """Replay exact signs and optional interval computations; no trust in CSV signs."""
    summary = json.loads((path.parent/'summary.json').read_text())
    assert summary['integers_checked'] == summary['limit_inclusive'] - 1
    assert hashlib.sha256(path.read_bytes()).hexdigest() == summary['csv_sha256']
    iv = ExactIntervals(summary['bits'], summary['log_and_exp_terms'], summary['gamma_m'])
    sig = sigma_sieve(summary['limit_inclusive'])
    failures = []
    count = 0
    with path.open(newline='') as stream:
        for row in csv.DictReader(stream):
            n, s, lo, hi, bits = [int(row[k]) for k in
                ['n','sigma','bound_lo_numerator','bound_hi_numerator','scale_power_of_two']]
            count += 1
            assert n == count+1 and s == sig[n] and bits == iv.bits and lo <= hi
            if recompute_intervals:
                assert iv.robin_bound(n) == Interval(lo,hi)
            if n*lo > s*iv.S:
                sign='holds'
            elif n*hi < s*iv.S:
                sign='fails'; failures.append(n)
            else:
                sign='undetermined'
            assert sign == row['sign'] and sign != 'undetermined'
    assert count == summary['integers_checked']
    assert failures == EXPECTED_EXCEPTIONS
    return {'rows_verified': count, 'failures': failures,
            'intervals_recomputed': recompute_intervals}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=100000)
    parser.add_argument('--output', type=Path, default=Path('../certificates'))
    parser.add_argument('--verify', type=Path)
    args = parser.parse_args()
    if args.verify:
        print(json.dumps(verify_csv(args.verify), indent=2))
    else:
        print(json.dumps(audit(args.limit, args.output), indent=2))
