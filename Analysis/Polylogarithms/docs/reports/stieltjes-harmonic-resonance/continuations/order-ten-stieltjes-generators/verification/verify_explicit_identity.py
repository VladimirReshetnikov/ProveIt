#!/usr/bin/env python3
from __future__ import annotations
import json
from fractions import Fraction
from pathlib import Path
from explicit_identity_core import derive_identity

HERE = Path(__file__).resolve().parent
PATH = HERE / "explicit_10_16_zeta2.json"
recorded = json.loads(PATH.read_text(encoding="utf-8"))
derived = derive_identity()
for key, value in derived.items():
    assert recorded[key] == value, key
assert len(recorded["polynomial_numerators"]) == 16
assert recorded["polynomial_numerators"][-1] != 0
assert set(recorded["subtraction"]) == {"0", "2", "4", "6"}
print("PASS: exact (10,16) -> zeta(2) reconstruction identity")
print(f"  P denominator: {recorded['polynomial_denominator']}")
print(f"  degree P: {2*(len(recorded['polynomial_numerators'])-1)}")
print(f"  degree Q: {max(map(int, recorded['subtraction']))}")
