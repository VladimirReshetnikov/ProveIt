"""Independent exploratory inversion of the normalized Fatou orbit.

The calculation is deliberately labelled non-certified: a truncated Fatou
coordinate initializes an orbit, and mpmath performs numerical inversion.
It is a normalization diagnostic, never a premise in the proofs.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp


def laplace_orbit(p, steps=160):
    """Return P(-p) by inversion near -p-steps and forward exponentiation."""
    a = [mp.mpf(-1) / 36, mp.mpf(1) / 540,
         mp.mpf(1) / 7776, -mp.mpf(71) / 435456]
    target = p + steps + mp.log(2) / 3
    u = target - mp.log(target) / 3
    for _ in range(12):
        w = 2 / u
        residual = u + mp.log(u) / 3 - sum(
            a[j - 1] * w**j for j in range(1, 5)) - target
        derivative = 1 + 1 / (3 * u) + sum(
            j * a[j - 1] * w**j / u for j in range(1, 5))
        correction = residual / derivative
        u -= correction
        if abs(correction) < mp.eps * abs(u) * 10:
            break
    w = 2 / u
    for _ in range(steps):
        w = mp.expm1(w)
    return w


def density(t, steps=160, degree=48):
    return mp.invertlaplace(lambda p: laplace_orbit(p, steps), t,
                           method="dehoog", degree=degree)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--steps", type=int, default=160)
    ap.add_argument("--degree", type=int, default=48)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    mp.mp.dps = 45
    rows = []
    for t in [mp.mpf("0.5"), mp.log(2), mp.mpf(1), mp.mpf(2)]:
        h = density(t, args.steps, args.degree)
        rows.append({"t": mp.nstr(t, 20), "h": mp.nstr(h, 20),
                     "I_from_bridge": mp.nstr(t * 2**(t / 3) * h, 20)})
    result = {"status": "exploratory, not interval certified",
              "fatou_truncation_order": 4, "steps": args.steps,
              "inversion_degree": args.degree, "rows": rows}
    out = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(out, encoding="utf-8")
    print(out, end="")


if __name__ == "__main__":
    main()
