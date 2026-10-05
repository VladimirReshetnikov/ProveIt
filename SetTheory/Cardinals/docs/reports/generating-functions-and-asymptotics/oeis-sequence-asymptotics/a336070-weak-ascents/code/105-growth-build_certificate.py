#!/usr/bin/env python3
"""Recreate the finite certificate; verification is a separate required step.

From the report directory:
    python3 code/build_certificate.py
    python3 code/run_checks.py
This builder does not certify the stored 501 terms. verify_exact.py regenerates
them and performs independent identity comparisons before reporting success.
"""
import json
from pathlib import Path
from exact_models import expected_certificate

if __name__ == "__main__":
    root = Path(__file__).resolve().parents[1]
    terms = (root / "data" / "weak_ascent_terms.txt").read_bytes()
    certificate = expected_certificate(terms)
    output = root / "data" / "exact_certificate.json"
    output.write_text(json.dumps(certificate, indent=2) + "\n", encoding="ascii")
    print(json.dumps({"status": "built_not_yet_verified", "certificate": str(output)}))
