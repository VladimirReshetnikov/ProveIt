#!/usr/bin/env python3
"""Command-line front end for the finite friendly-order-type engine.

Usage:

    python3 code/friendly_cli.py examples/diamond.json --dp

The input is a JSON object ``{"n": ..., "relations": [[a, b], ...]}`` whose
relations are *strict generating* relations (Hasse edges are acceptable); the
program takes their transitive closure and rejects cycles and out-of-range
labels.  Labels are integers ``0,...,n-1`` and need not themselves form a
linear extension.  The optional key ``"roots": [...]`` prescribes exactly one
root per incomparability component, each minimal inside its own component.

``--dp`` additionally runs the independent exponential residual recursion,
which does not use the component formula.  Avoid it for large posets: the
formula itself is quadratic on a comparison matrix, but the reference
recursion may visit up to 2**n subsets.

Python 3.10+, standard library only.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from friendly import Poset, bits  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("input", type=Path,
                        help='JSON object {"n":..., "relations":[[a,b],...]}')
    parser.add_argument("--dp", action="store_true",
                        help="Also run the exponential direct residual recursion")
    args = parser.parse_args()
    try:
        data = json.loads(args.input.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            raise ValueError("Input must be a JSON object")
        poset = Poset.from_relations(data["n"], data.get("relations", []))
        certificate = poset.optimal_certificate(data.get("roots"))
        poset.check_certificate(certificate)
        output = {"n": poset.n,
                  "incomparability_components":
                      [list(bits(c)) for c in poset.ordered_components()],
                  "friendly_order_type": poset.friendly(),
                  "multiset_ordinal_width": f"omega^({poset.friendly()})",
                  "certificate": certificate}
        if args.dp:
            output["independent_residual_rank"] = poset.friendly_dp()
        print(json.dumps(output, indent=2))
    except (OSError, KeyError, TypeError, ValueError) as exc:
        parser.exit(2, f"error: {exc}\n")


if __name__ == "__main__":
    main()
