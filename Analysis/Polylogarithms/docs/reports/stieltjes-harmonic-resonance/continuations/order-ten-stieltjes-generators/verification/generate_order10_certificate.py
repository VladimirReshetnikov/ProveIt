#!/usr/bin/env python3
from __future__ import annotations
import json
from datetime import date
from pathlib import Path
from order10_core import (
    A, B_MAX, B_MIN, B_RETAINED_MIN, MAX_FACTORIAL, MAX_MATRIX_FACTORIAL, PRIME,
    compute_all_residues, residue_digest,
)

HERE = Path(__file__).resolve().parent
OUT = HERE / "order10_modular_certificate.json"

residues = compute_all_residues()
if any(r == 0 for r in residues):
    raise SystemExit("zero residue found; certificate cannot be emitted")

payload = {
    "schema": "proveit.order-ten-modular-certificate.v2",
    "generated": str(date(2026, 10, 11)),
    "claim": (
        "all published proof residues are nonzero; with the exact multiplier theorem "
        "this proves det(M_{5,b}) != 0 for every integer 6 <= b < 1920"
    ),
    "repository_snapshot": "04bf92d507588a26abadbaee1beb1e7350c8bffb",
    "residue_definition": {
        "6<=b<=9": "det(M_{5,b}) modulo P",
        "10<=b<=1919": (
            "det(A^[5](b; 2B_{2b-2},...,2B_{2b-18})) modulo P; "
            "nonvanishing is equivalent to det(M_{5,b})!=0 by the inherited exact multiplier"
        ),
    },
    "canonical_encoding": (
        "ASCII decimal representatives r_6,...,r_1919 in [1,P-1], joined by commas "
        "with no spaces and no terminal newline before SHA-256"
    ),
    "prime": PRIME,
    "a": A,
    "smaller_tail_order": 2 * A,
    "b_min": B_MIN,
    "b_max": B_MAX,
    "count": len(residues),
    "direct_matrix_range": [B_MIN, B_RETAINED_MIN - 1],
    "retained_matrix_range": [B_RETAINED_MIN, B_MAX],
    "max_factorial_argument": MAX_MATRIX_FACTORIAL,
    "factorial_table_limit": MAX_FACTORIAL,
    "max_bernoulli_index_used": 2 * (B_MAX - 1),
    "max_bernoulli_index_generated": 2 * B_MAX,
    "max_multiplier_factorial_argument": 4 * (B_MAX - 1) + 2,
    "all_residues_nonzero": True,
    "primary_replay": "even Bernoulli recurrence plus modular Gaussian elimination",
    "independent_replay": (
        "full Bernoulli recurrence plus row-wise subset-expansion determinants; "
        "does not import order10_core.py"
    ),
    "residue_sha256": residue_digest(residues),
    "sentinels": {
        "b=6": residues[6 - B_MIN],
        "b=8": residues[8 - B_MIN],
        "b=10": residues[10 - B_MIN],
        "b=962": residues[962 - B_MIN],
        "b=1919": residues[1919 - B_MIN],
    },
    "residues": residues,
}
OUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps({k: payload[k] for k in ["count", "prime", "residue_sha256", "sentinels"]}, indent=2))
