#!/usr/bin/env python3
"""Reproduce one packaged deterministic search, then verify its output.

Run make first, then python scripts/reproduce.py --n 10.
The default reproduces the original 14-point n10 certificate.
"""
import argparse
import json
import subprocess
import tempfile
from pathlib import Path
from verify_bundle import verify


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n",type=int,default=10)
    parser.add_argument("--all",action="store_true")
    args=parser.parse_args()
    root=Path(__file__).resolve().parent.parent
    manifest=json.loads((root/"data"/"reproduction_manifest.json").read_text())
    selected=manifest if args.all else [r for r in manifest if r["n"]==args.n]
    if not selected:raise ValueError("No reproduction recipe for requested size")
    for recipe in selected:
        with tempfile.TemporaryDirectory() as tmp:
            output=Path(tmp)/"output.json"
            command=[str(root/"bin"/recipe["program"]),str(recipe["n"]),
                     str(recipe["input_k"]),str(recipe["seed"]),
                     str(-recipe["iterations"])]
            if recipe.get("starting_points"):
                command.extend([str(root/recipe["starting_points"]),str(output)])
            else:command.append(str(output))
            subprocess.run(command,check=True)
            actual=json.loads(output.read_text())
            expected=json.loads((root/recipe["expected_output"]).read_text())
            verify(actual);verify(expected)
            if actual["points"]!=expected["points"]:
                raise AssertionError(f"Different output for n={recipe['n']}")
            print(f"n={recipe['n']}: exact point-for-point reproduction PASS")


if __name__=="__main__":main()
