#!/usr/bin/env python3
"""Synthetic search sanity control. Generated tables are NOT ZFC candidates."""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys
sys.dont_write_bytecode = True
from run_census import ROOT, compile_scanner, digest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "control_replay")
    parser.add_argument("--compiler", default=os.environ.get("CXX", "g++"))
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    base = ROOT / "inputs/k215.native.tm"
    assert digest(base) == "9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2"
    table = {}
    for line in base.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        q, b, w, d, z = line.split()
        table[int(q), int(b)] = (int(w), d, int(z))
    assert table[8, 0] == (0, "R", 14) and table[59, 0] == (0, "R", 62)
    table[8, 1] = (1, "R", 99)
    table[59, 1] = (1, "R", 52)
    artificial = out / "NOT_A_ZFC_CANDIDATE.tm"
    artificial.write_text("#! start 0\n" + "".join(
        f"{q} {b} {w} {d} {z}\n" for (q, b), (w, d, z) in sorted(table.items())))
    executable = compile_scanner("same", out / "build", args.compiler)
    prefix = out / "synthetic-only"
    with prefix.with_suffix(".log").open("w") as log:
        subprocess.run([str(executable), str(artificial), "124", str(prefix), "0"],
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    result = json.loads(prefix.with_suffix(".json").read_text())
    assert result["survivors"] == 2 and result["candidates"] == 5861888
    result["warning"] = "Artificial input and its two hits have no ZFC calibration; do not treat them as ZFC candidates."
    result["artificial_input_sha256"] = digest(artificial)
    (out / "CONTROL_ONLY_result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
