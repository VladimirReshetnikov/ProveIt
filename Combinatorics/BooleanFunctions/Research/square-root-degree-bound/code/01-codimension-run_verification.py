#!/usr/bin/env python3
"""Reproduce the exact witness and, optionally, the minimality enumeration.

Default: verify all grouped witness cells and their complete high-degree
Walsh coefficient profiles.  --exhaustive also enumerates the four cases
needed for the explicitly scoped twenty-bit minimality result.  Both modes
use the Python standard library and exact arithmetic only.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from enumerate_reporters import enumerate_all
from verify_witness import verify


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive", action="store_true", help="rerun all 1,731,542 minimality configurations")
    parser.add_argument("--data-dir", type=Path, default=Path(__file__).resolve().parent.parent / "data")
    args = parser.parse_args()
    args.data_dir.mkdir(parents=True, exist_ok=True)
    witness = verify()
    (args.data_dir / "witness_certificate.json").write_text(json.dumps(witness, indent=2) + "\n", encoding="utf-8")
    print("PASS: twenty-bit witness, 622 exact-degree-16 cells, retained variance 16 + 9/34816.", flush=True)
    if args.exhaustive:
        minimality = enumerate_all()
        (args.data_dir / "minimality_certificate.json").write_text(json.dumps(minimality, indent=2) + "\n", encoding="utf-8")
        print("PASS: all 1,731,542 configurations in the scoped minimality enumeration.", flush=True)
    else:
        print("Minimality enumeration was not rerun; use --exhaustive to reproduce it.")


if __name__ == "__main__":
    main()
