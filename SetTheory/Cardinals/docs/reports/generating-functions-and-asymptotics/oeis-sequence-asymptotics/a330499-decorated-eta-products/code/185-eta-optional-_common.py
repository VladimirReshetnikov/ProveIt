"""Shared I/O and exact-integer inputs for optional numerical diagnostics.

This module has no third-party dependencies. No file is changed at import.
"""
import argparse
import importlib.util
from functools import lru_cache
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
BOUNDARY = (
    "Finite floating-point regression only; not an interval certificate, proof of "
    "a uniform asymptotic remainder, or certified integer inverse threshold."
)


def require(condition, message):
    """Explicit guard; remains active under python -O."""
    if not condition:
        raise RuntimeError(message)


def odd_sigma(k):
    require(isinstance(k, int) and k >= 1, "odd_sigma requires a positive integer")
    return sum(d for d in range(1, k + 1, 2) if k % d == 0)


def fallback_exact_values(nmax):
    """Standalone exact unsigned-Stirling transform, no numerical approximation."""
    require(isinstance(nmax, int) and 0 <= nmax <= 2000,
            "standalone exact range is 0 <= max_n <= 2000")
    factorials = [math.factorial(k) for k in range(nmax + 1)]
    weights = [0] + [factorials[k - 1] * odd_sigma(k)
                     for k in range(1, nmax + 1)]
    row, out = [1], [0]
    for n in range(1, nmax + 1):
        row = [0] + [row[k - 1] + (n - 1) * (row[k] if k < len(row) else 0)
                     for k in range(1, n + 1)]
        out.append(sum(row[k] * weights[k] for k in range(1, n + 1)))
    return out


@lru_cache(maxsize=4)
def exact_inputs(nmax, standalone=False):
    """Use the public exact kernel when present; otherwise identify the fallback."""
    require(isinstance(nmax, int) and 1 <= nmax <= 2000,
            "optional exact-input range is 1 <= max_n <= 2000")
    path = Path(__file__).resolve().parents[1] / "code" / "verify_exact.py"
    if not standalone and path.is_file():
        spec = importlib.util.spec_from_file_location("report185_verify_exact", path)
        require(spec is not None and spec.loader is not None, "cannot load exact kernel")
        kernel = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(kernel)
        require(callable(getattr(kernel, "exact_values", None)),
                "public exact kernel does not expose exact_values(N)")
        values = kernel.exact_values(nmax)
        engine = "code/verify_exact.py:exact_values"
    else:
        values = fallback_exact_values(nmax)
        engine = "optional/_common.py:fallback_exact_values"
    require(len(values) == nmax + 1 and values[0] == 0 and values[1] == 1,
            "exact-input shape or initial values are invalid")
    require(all(isinstance(v, int) and v > 0 for v in values[1:]),
            "exact inputs must be positive Python integers")
    return values, engine


def parser(description):
    p = argparse.ArgumentParser(description=description)
    p.add_argument("--output", type=Path,
                   help="write JSON to a NEW file instead of stdout; never overwrite")
    return p


def emit_json(receipt, output=None):
    payload = json.dumps(receipt, indent=2, sort_keys=True, allow_nan=False) + "\n"
    if output is None:
        sys.stdout.write(payload)
    else:
        # Exclusive creation protects scripts, input files and previous receipts.
        with output.open("x", encoding="utf-8") as stream:
            stream.write(payload)


def check_indices(indices, nmax, minimum=1):
    require(bool(indices) and all(isinstance(n, int) and minimum <= n <= nmax
                                 for n in indices), "sample indices out of bounded range")
    return sorted(set(indices))
