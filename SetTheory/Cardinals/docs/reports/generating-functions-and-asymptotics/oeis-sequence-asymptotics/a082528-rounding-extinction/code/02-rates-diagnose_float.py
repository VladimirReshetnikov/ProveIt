#!/usr/bin/env python3
"""Optional floating diagnostics. NOT an interval or exact certificate.

This script is deliberately separate from check_exact.py. Its use of platform
math.gamma and floating powers may have rounding error; decimal output is not
claimed portable or byte-identical across Python/libm platforms.
"""
import argparse
from fractions import Fraction
import importlib.util
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("report188_diagnostic_exact", HERE / "exact_rounding.py")
if SPEC is None or SPEC.loader is None:
    raise ImportError("Cannot load exact_rounding.py")
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)


def run():
    rows = []
    for p in (Fraction(1, 2), Fraction(1), Fraction(3, 2), Fraction(2), Fraction(3), Fraction(4)):
        floating_p = float(p)
        c = floating_p * math.gamma(floating_p / (floating_p + 1)) ** (floating_p + 1)
        for k in (100, 1000, 10000):
            boundary = M.threshold(k, p)
            main_term = k ** (floating_p + 1) / c
            rows.append({"p": str(p), "k": k, "exact_threshold": boundary,
                         "diagnostic_c": c, "diagnostic_threshold_over_main_term": boundary / main_term})
    return {"status": "diagnostic_only", "certified_interval": False,
            "warning": "Floating Gamma evaluations and ratios are diagnostics only; they do not verify any asymptotic error bound or certify decimal intervals.",
            "rows": rows}


def write_output(path, text):
    """Create a fresh nonsymlink output outside the immutable source package."""
    target = path.absolute()
    for component in (target, *target.parents):
        if component.is_symlink():
            raise ValueError("output path must not contain symlinks")
    resolved = target.resolve()
    source_root = HERE.parent.resolve()
    if resolved == source_root or source_root in resolved.parents:
        raise ValueError("output must be outside the source package")
    if not target.parent.is_dir():
        raise ValueError("output parent directory must already exist")
    with target.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(run(), indent=2, sort_keys=True, allow_nan=False) + "\n"
    if args.output is not None:
        write_output(args.output, result)
    print(result, end="")


if __name__ == "__main__":
    main()
