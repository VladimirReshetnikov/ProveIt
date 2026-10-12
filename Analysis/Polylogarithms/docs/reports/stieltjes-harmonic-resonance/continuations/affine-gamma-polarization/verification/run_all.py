#!/usr/bin/env python3
"""Replay all exact checks and numerical diagnostics, then record a summary.

Run with ordinary Python, not python -O: exact-check scripts use assertions.
No repository checkout or network access is required.
"""
from __future__ import annotations
import json
import argparse
import platform
import subprocess
import sys
from pathlib import Path
import mpmath
import sympy

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    if not __debug__:
        raise SystemExit("Assertion-disabling optimization is unsupported; omit -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--summarize-only", action="store_true", help="Aggregate existing result files without rerunning checks.")
    args = parser.parse_args()
    scripts = ["check_algebra.py", "check_endpoint_algebra.py", "check_profiles.py",
               "check_selectors.py"]
    commands = [[sys.executable, str(ROOT / "verification" / name)] for name in scripts]
    commands += [[sys.executable, str(ROOT / "verification" / "check_numeric.py"),
                  "--part", part] for part in ("kernel", "transform", "stieltjes", "extras")]
    for command in ([] if args.summarize_only else commands):
        print("\nREPLAY:", " ".join(command), flush=True)
        subprocess.run(command, cwd=ROOT, check=True)
    data = ROOT / "data"
    exact = [json.loads((data / name).read_text()) for name in
             ("algebra_results.json", "endpoint_algebra_results.json",
              "profile_results.json", "selector_results.json")]
    numeric = [json.loads((data / f"numeric_{part}_results.json").read_text()) for part in
               ("kernel", "transform", "stieltjes", "extras")]
    summary = {
        "status": "PASS",
        "exact_assertions": sum(d["exact_assertions"] for d in exact),
        "numerical_comparisons": sum(d["comparisons"] for d in numeric),
        "python": platform.python_version(), "sympy": sympy.__version__,
        "mpmath": mpmath.__version__, "exact_parts": exact,
        "numerical_parts": [{k: v for k, v in d.items() if k != "results"} for d in numeric],
        "scope": "Finite exact assertions and floating-point diagnostics. Infinite families are proved in the article; no interval or proof-assistant certification."
    }
    (data / "verification_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k:v for k,v in summary.items() if not k.endswith("parts")}, indent=2))


if __name__ == "__main__":
    main()
