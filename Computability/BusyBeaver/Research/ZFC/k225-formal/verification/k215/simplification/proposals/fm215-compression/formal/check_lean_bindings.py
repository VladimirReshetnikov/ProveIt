#!/usr/bin/env python3
"""Bind FM215Data.lean's complete literal tables to the exact .tm artifacts.

This independent byte/data audit accompanies the Lean kernel theorem.  It
does not replace the compiler; it confirms that the compiled literals are
the intended machine inputs.  There is no Lean execution in this script.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

OLD_SHA = "9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2"
NEW_SHA = "3ece1233f11d33375425221c5bcedba941e073763912990eabf321197772dce5"


def require(test, message):
    if not test:
        raise ValueError(message)


def parse_machine(path, expected):
    raw = path.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == expected, "Machine hash mismatch")
    rows = {}
    for line in raw.decode().splitlines():
        if line and not line.startswith("#"):
            q, b, w, d, z = line.split()
            key = int(q), int(b)
            require(key not in rows, "Duplicate machine row")
            rows[key] = int(w), d == "R", int(z)
    return rows


def main():
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=root / "FM215Data.lean")
    parser.add_argument("--old", type=Path, default=root / "k215.native.tm")
    parser.add_argument("--new", type=Path, default=root / "fm215.native.tm")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = args.data.read_text()
    require("abbrev State := Fin 512" in text, "Wrong finite ambient label bound")
    results = {}
    pattern = r"  \| (\d+), (false|true) => some \((false|true), (false|true), (\d+)\)"
    for name, path, sha in [("old", args.old, OLD_SHA), ("new", args.new, NEW_SHA)]:
        literal = text.split(f"def {name} (q : State) (b : Bool) : Option Action :=\n  match q.val, b with\n", 1)[1]
        body, remainder = literal.split("  | _, _ => none", 1)
        rows = {}
        for line in body.splitlines():
            match = re.fullmatch(pattern, line)
            require(match is not None, "Unrecognized Lean table row: " + line)
            q, b, w, d, z = match.groups()
            key = int(q), int(b == "true")
            require(key not in rows, "Duplicate Lean table row")
            require(int(q) < 512 and int(z) < 512, "Fin literal would wrap")
            rows[key] = int(w == "true"), d == "true", int(z)
        expected = parse_machine(path, sha)
        require(rows == expected and len(rows) == 430, "Literal table mismatch")
        results[name] = {"machine_sha256": sha, "rows": len(rows), "all_literals_bound": True}
    for source in [root / "PositiveSimulation.lean", args.data, root / "FM215.lean"]:
        require(source.exists(), "Missing formal source")
        # Conservative token scan; the separate kernel receipt reports dependencies.
        require(not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", source.read_text()),
                "Unexpected trust-gap token in formal source")
    report = {
        "status": "PASS_EXACT_LITERAL_BINDINGS",
        "tables": results,
        "lean_data_sha256": hashlib.sha256(args.data.read_bytes()).hexdigest(),
        "note": "Finite ambient labels are not a state count; only 215 controls have rows.",
    }
    out = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(out)
    print(out, end="")


if __name__ == "__main__":
    main()
