#!/usr/bin/env python3
"""Reproduce finite A088714/A088713 normalization diagnostics.

Python 3.11+ standard library only. Decimal Newton arithmetic is a
high-precision stability check, not certified interval arithmetic.

Example:
    python normalization_diagnostics.py --max-index 600 --precision 80 \
        --coefficients coefficients_600.txt --output normalization_80.json

If --coefficients exists, it must contain complete lines "n a_n".
If it does not exist, the exact triangular recurrence regenerates it.
The n=600 generation took about 35 seconds on the research runtime.
"""
import argparse
from decimal import Decimal, localcontext
import json
from pathlib import Path

from verify_complement import coefficients


def lambert_w_positive(n, precision):
    """Positive real W(n), by Decimal Newton iteration with guard digits."""
    if n == 0:
        return Decimal(0)
    x = Decimal(n)
    if n > 3:
        logx = x.ln()
        w = logx - logx.ln()
    else:
        w = Decimal("0.5")
    tolerance = Decimal(10) ** (-(precision + 8))
    for _ in range(100):
        ew = w.exp()
        correction = (w * ew - x) / ((w + 1) * ew)
        w -= correction
        if abs(correction) < tolerance:
            return w
    raise ArithmeticError("Lambert W Newton iteration did not converge")


def log_normalizer(n, precision):
    if n == 0:
        return Decimal(0)
    x = Decimal(n)
    w = lambert_w_positive(n, precision)
    return (x * (w - 1 + 1 / w) - 1
            + w * w + 3 * w - (1 + w).ln() / 2)


def load_or_generate(path, count):
    if path.exists():
        values = []
        for line in path.read_text().splitlines():
            if not line.strip():
                continue
            n, value = line.split()
            if int(n) != len(values):
                raise ValueError("Coefficient indices must be consecutive from 0")
            values.append(int(value))
        if len(values) <= count:
            raise ValueError("Coefficient file does not reach --max-index")
        return values[:count + 1]
    values = coefficients(count)
    path.write_text("".join(f"{n} {value}\n"
                           for n, value in enumerate(values)))
    return values


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-index", type=int, default=600)
    parser.add_argument("--precision", type=int, default=80)
    parser.add_argument("--coefficients", type=Path,
                        default=Path("coefficients_600.txt"))
    parser.add_argument("--output", type=Path,
                        default=Path("normalization_diagnostics.json"))
    args = parser.parse_args()
    if args.max_index < 25:
        parser.error("--max-index must be at least 25")
    if args.precision < 40:
        parser.error("--precision must be at least 40")
    a = load_or_generate(args.coefficients, args.max_index)

    c = [1]
    for n in range(1, args.max_index + 1):
        c.append(sum(a[j] * c[n - 1 - j] for j in range(n)))
    assert a[:7] == [1, 1, 3, 13, 69, 419, 2809]
    assert c[:10] == [1, 1, 2, 6, 24, 118, 674, 4308, 30062, 225266]

    indices = [n for n in (25, 50, 100, 200, 400, 600)
               if n <= args.max_index]
    if args.max_index not in indices:
        indices.append(args.max_index)
    rows = []
    with localcontext() as ctx:
        ctx.prec = args.precision + 20
        for n in indices:
            x = Decimal(n)
            w = lambert_w_positive(n, args.precision)
            logn = log_normalizer(n, args.precision)
            row = {
                "n": n,
                "W_n": format(w, ".24f"),
                "a_n_over_N_n": format((Decimal(a[n]).ln() - logn).exp(),
                                       ".30f"),
                "r_n_minus_n_over_W_n":
                    format(Decimal(a[n]) / Decimal(a[n - 1]) - x / w,
                           ".24f"),
                "c_n_over_a_n_minus_1":
                    format(Decimal(c[n]) / Decimal(a[n - 1]), ".24f"),
            }
            rows.append(row)

    result = {
        "exact_terms_through": args.max_index,
        "decimal_precision": args.precision,
        "guard_digits": 20,
        "method": "exact triangular recurrence, Decimal Newton W, Decimal exp/ln",
        "rows": rows,
        "limitations": [
            "Finite diagnostics do not prove the asymptotic theorems.",
            "The displayed normalized values are not certified bounds on C_*.",
            "Decimal arithmetic here is not interval arithmetic.",
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

