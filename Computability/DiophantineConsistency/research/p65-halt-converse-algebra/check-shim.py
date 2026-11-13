#!/usr/bin/env python3
"""Verify the P65 graph shim differs from the retained source only in imports."""
from hashlib import sha256
from pathlib import Path
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
source = (BASE / "Lean/DiophantineConsistency/Compact44/P65Graph.lean").read_bytes()
shim = (HERE / "P65GraphShim.lean").read_bytes()
assert sha256(source).hexdigest() == "78a40f3bab902668e739e0068407808d094780409a002326f9dd745c53656338"
assert sha256(shim).hexdigest() == "83e122b6ce29a9f9eeee5538ac0a8dff4962f470baef8f532e095fd0ed4399e1"
old = b"import DiophantineConsistency.Compact44.FreeJSumSquares\n"
new = (b"import DiophantineConsistency.AdaptiveEquationSyntax2011\n"
       b"import DiophantineConsistency.ModelDifferenceRing\n"
       b"import DiophantineConsistency.ArithmeticPow\n")
assert source.startswith(old) and shim == new + source[len(old):]
print("PASS: graph shim is byte-identical after the three replacement imports")
print("This external comparison is not a coherent canonical source rebuild.")
