#!/usr/bin/env python3
"""Regenerate the exact continued-fraction traces supplied with the article."""
import json
from pathlib import Path

from pell_reference import cf_certificate


examples = [cf_certificate(D) for D in (2, 3, 7, 12, 13, 34, 61)]
document = {
    "kind": "finite arithmetic traces, not embedded iPRA proof certificates",
    "generator": "export_certificates.py using pell_reference.py",
    "examples": examples,
}
destination = Path(__file__).with_name("cf-certificates.json")
destination.write_text(json.dumps(document, indent=2) + "\n", encoding="utf-8")
print(f"Wrote {len(examples)} exact CF traces to {destination.name}")
