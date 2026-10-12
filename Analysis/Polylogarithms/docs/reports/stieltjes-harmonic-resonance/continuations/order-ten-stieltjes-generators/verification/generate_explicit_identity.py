#!/usr/bin/env python3
from __future__ import annotations
import json
from pathlib import Path
from explicit_identity_core import derive_identity

HERE = Path(__file__).resolve().parent
OUT = HERE / "explicit_10_16_zeta2.json"
obj = derive_identity()
obj["schema"] = "proveit.harmonic-tail-ordinary-identity.v1"
obj["claim"] = (
    "sum_{n>=0}(P(n+1/2) A_10(n) A_16(n) - Q(n+1/2)) = zeta(2), "
    "where A_s(n)=zeta(s)-H_n^(s)"
)
OUT.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps({k: obj[k] for k in ["p", "q", "zeta_value", "polynomial_denominator", "subtraction"]}, indent=2))
