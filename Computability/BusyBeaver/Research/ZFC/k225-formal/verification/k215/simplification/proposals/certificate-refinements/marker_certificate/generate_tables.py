#!/usr/bin/env python3
"""Generate the literal Coq tables from the shipped native machine files."""
from pathlib import Path
import argparse

NAMES = ("K215", "M124", "FM215", "M125")

def parse(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        q, b, w, d, z = line.split()
        key = int(q), int(b)
        if key in rows or d not in ("L", "R") or int(b) not in (0, 1) or int(w) not in (0, 1):
            raise ValueError(f"Invalid or duplicate row in {path.name}: {line}")
        rows[key] = int(w), d, int(z)
    return rows

def render(root):
    lines = ["(* Generated exactly from the four included native .tm files. *)",
             "From Coq Require Import Lists.List.", "Require Import MarkerFold.",
             "Import ListNotations.", ""]
    for name in NAMES:
        rows = parse(root / (name + ".tm"))
        def expression(q, bit):
            if (q, bit) not in rows:
                return "None"
            w, d, z = rows[q, bit]
            return f"Some (I {str(bool(w)).lower()} {str(d == 'R').lower()} {z})"
        lines.append(f"Definition {name} : table := [")
        lines.extend("  (" + expression(q, 0) + ", " + expression(q, 1) + ")" +
                     (";" if q < 302 else "") for q in range(303))
        lines.append("].\n")
    return "\n".join(lines) + "\n"

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    generated = render(root)
    if args.output:
        args.output.write_text(generated)
    else:
        if generated != (root / "MarkerTables.v").read_text():
            raise SystemExit("Literal table regeneration mismatch")
        print("All four Coq tables regenerate exactly from native rows.")
