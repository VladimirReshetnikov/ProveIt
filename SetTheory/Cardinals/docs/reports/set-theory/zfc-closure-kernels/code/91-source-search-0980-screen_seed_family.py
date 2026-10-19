#!/usr/bin/env python3
"""Run bounded fine-grammar searches and independently audit every output.

This is a heuristic search driver, not a proof of logical calibration or of
the complete binary machine. It preserves each seed's explicit source override.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("fine", type=Path)
    p.add_argument("seeds", type=Path)
    p.add_argument("binary", type=Path)
    p.add_argument("--seconds", type=float, default=4)
    p.add_argument("--seed-offset", type=int, default=18001000)
    p.add_argument("--skip", type=int, action="append", default=[])
    p.add_argument("--only", type=int, action="append")
    p.add_argument("--label", default="screen")
    a = p.parse_args()
    sys.path.insert(0, str(a.fine.resolve() / "runtime/code"))
    from audit_fine_grammar import audit
    rows = []
    for directory in sorted(a.seeds.glob("mask*")):
        ident = int(directory.name[4:])
        if ident in a.skip or (a.only is not None and ident not in a.only):
            continue
        seed = json.loads((directory / "seed.json").read_text())
        raw = directory / (a.label + "_raw.json")
        cmd = [str(a.binary.resolve()), str(directory / "grammar.txt"),
               str(directory / "constraints.txt"), str(raw), str(a.seconds),
               str(a.seed_offset + ident), "127",
               str(a.fine / "fine-lock54.txt"), str(directory / "resume.txt")]
        log = directory / (a.label + ".log")
        with log.open("w") as out:
            subprocess.run(cmd, stdout=out, stderr=subprocess.STDOUT, check=True)
        data = json.loads(raw.read_text())
        data["source_override"] = seed["source_override"]
        dest = directory / (a.label + ".json")
        dest.write_text(json.dumps(data, indent=2) + "\n")
        result = audit(dest, short_scan=True)
        dest.with_suffix(".audit.json").write_text(json.dumps(result, indent=2) + "\n")
        rows.append(dict(identifier=ident, rewrite=seed["source_override"].get("rewrite_name"),
                         initial_rules=seed["rules_count"], final_rules=data["rules_count"],
                         iterations=data["iterations"], seconds=data["seconds"],
                         properties=data["properties"], audit=result["status"],
                         candidate=str(dest), sha256=hashlib.sha256(dest.read_bytes()).hexdigest()))
        (a.seeds / (a.label + "_summary.json")).write_text(json.dumps(rows, indent=2) + "\n")
        print(json.dumps(rows[-1]), flush=True)
        if data["rules_count"] <= 127:
            break


if __name__ == "__main__":
    main()
