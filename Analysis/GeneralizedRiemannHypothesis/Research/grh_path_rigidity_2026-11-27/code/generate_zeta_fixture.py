#!/usr/bin/env python3
"""Regenerate the illustrative zeta fixture (not a rigorous interval certificate)."""
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps = 30
rows = [{"n": n, "gamma": mp.nstr(mp.im(mp.zetazero(n)), 28)}
        for n in range(1, 151)]
out = Path(__file__).resolve().parents[1] / "data/zeta_first_150.json"
out.write_text(json.dumps({
    "description": "Numerical illustration only: first 150 positive zeta zeros computed with mpmath at 30 decimal digits. Not interval-certified. Multiplicity one is used only for this finite illustration.",
    "mpmath_version": mp.__version__,
    "working_decimal_precision": 30,
    "zeros": rows,
}, indent=2) + "\n")
print(out)
