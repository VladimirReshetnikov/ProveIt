#!/usr/bin/env python3
"""Compare the two exact natural encodings to the rational target."""

from __future__ import annotations
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import arithmetic_spec as raw
import integer_spec as common


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    instances = [(0, 0), (0, 127), (0, 128), (0, 135), (0, 256),
                 (1, 512), (1, 519), (2, 2048)]
    checked = []
    for k, n in instances:
        assert raw.target(k, n)
        assert common.check(k, n)
        if n >= raw.cutoff(k):
            f, b, c = common.components(k, n)
            z = raw.square_partial(n)
            p = raw.pi_partial(k)
            assert Q(b, f*f) == Q(z.numerator, z.denominator)
            assert Q(4*c, f) == Q(p.numerator, p.denominator)
            assert abs(6*Q(b, f*f) - 16*Q(c, f)**2) <= Q(1, 2**k)
        checked.append({"k": k, "n": n, "cutoff": raw.cutoff(k), "passed": True})
    report = {
        "status": "passed",
        "scope": "finite exact encoding checks, not a universal formal proof",
        "instances": checked,
        "claims": [
            "unreduced natural fractions evaluate the displayed arithmetic target",
            "factorial denominator gives the same S_n and P_k",
            "both total checkers accept false-antecedent cases",
        ],
    }
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
