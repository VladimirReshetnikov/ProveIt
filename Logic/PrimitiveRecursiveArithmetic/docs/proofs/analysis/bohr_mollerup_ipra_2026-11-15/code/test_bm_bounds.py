#!/usr/bin/env python3
"""Small exact-arithmetic regression tests for bm_bounds.py."""

from dataclasses import asdict
from fractions import Fraction

from bm_bounds import gamma_certificate, verify_certificate


def run() -> None:
    cases = [
        (Fraction(1, 2), 5),
        (Fraction(1, 1), 6),
        (Fraction(3, 2), 4),
        (Fraction(5, 3), 3),
    ]
    for x, bits in cases:
        cert = gamma_certificate(x, bits)
        verify_certificate(asdict(cert))
        lo = Fraction(cert.lower)
        hi = Fraction(cert.upper)
        assert lo <= hi
        assert hi - lo <= Fraction(1, 1 << bits)
        print(f"ok: x={x}, bits={bits}, n={cert.n}, width <= 2^-{bits}")


if __name__ == "__main__":
    run()
