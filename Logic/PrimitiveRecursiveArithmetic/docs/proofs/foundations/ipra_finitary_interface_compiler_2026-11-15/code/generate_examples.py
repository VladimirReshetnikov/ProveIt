from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from finitary_kernel import cubic_inverse_certificate

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "examples" / "cubic_inverse_x2_q12.json"

cert = cubic_inverse_certificate(Fraction(2), 12)
OUT.write_text(json.dumps(cert, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(OUT)
