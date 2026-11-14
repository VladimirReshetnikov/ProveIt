#!/usr/bin/env python3
"""Bind the inherited AX11 emitter and four-field decoder to AX11H.

Only the unchanged emitter and decoder checks are reused. The old AX11
sum-Shift word checker is deliberately not called: check_words.py checks
the changed AX11H protocol separately.
"""
from pathlib import Path
import argparse
import hashlib
import json
import reference_ax11_commands as inherited

ROOT = Path(__file__).resolve().parent.parent


def check(machine):
    return {
        "status": "PASS",
        "family": "PA194AX11H",
        "emitter": inherited.emitter(machine),
        "scheduler": inherited.scheduler_check(),
        "scope": "Unchanged AX11 emitter and four-field decoder only; AX11H words are checked separately.",
        "inputs": {name: hashlib.sha256((machine / name).read_bytes()).hexdigest()
                   for name in ("grammar.tree.json", "nodes.json", "machine.tm")},
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--machine", type=Path, default=ROOT / "machine")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = check(args.machine)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
