#!/usr/bin/env python3
"""Run every exact replay and every numerical diagnostic in package order."""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = [
    "generate_order10_certificate.py",
    "verify_order10_certificate.py",
    "verify_order10_certificate_independent.py",
    "verify_normalization_spots.py",
    "generate_explicit_identity.py",
    "verify_explicit_identity.py",
    "numerical_check_explicit_identity.py",
    "numerical_check_generators.py",
]

for name in SCRIPTS:
    print(f"\n===== {name} =====", flush=True)
    subprocess.run([sys.executable, str(ROOT / "verification" / name)], cwd=ROOT, check=True)

print("\nPASS: complete package replay")
