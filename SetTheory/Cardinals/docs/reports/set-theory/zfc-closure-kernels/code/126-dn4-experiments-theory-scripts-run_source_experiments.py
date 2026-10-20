#!/usr/bin/env python3
"""Portable launcher for the source-grammar discovery experiments.

The source/builder/Dag230 inputs are supplied explicitly.  This launcher
does not compile or certify a binary TM.  Run with assertions enabled.
"""
from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import sys

import verify_full_dn_semantics as v


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("experiment", choices=("full-dn", "selectors", "logical-rows", "swap-ab", "ksp", "ksp-parameters", "ks-dne", "ks-dne-parameters", "ks-clavius", "ks-clavius-parameters", "canonical-ve"))
    for name in ("baseline", "builder", "dag", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--dn4", type=Path)
    args = parser.parse_args()
    for path, expected in ((args.baseline, v.BASELINE_SHA256), (args.builder, v.BUILDER_SHA256), (args.dag, v.DAG_SHA256)):
        v.require(hashlib.sha256(path.read_bytes()).hexdigest() == expected, "Incorrect pinned input: " + str(path))
    scripts = {
        "full-dn": ["full_dn_variants.py"],
        "selectors": ["selector_permutations.py"],
        "logical-rows": ["logical_row_permutations.py"],
        "swap-ab": ["axiom_parameter_permutations.py"],
        "ksp": ["estimate_ksp.py"],
        "ksp-parameters": ["estimate_ksp.py", "--parameter-permutations", "--basis", "dn4"],
        "ks-dne": ["estimate_ks_classical.py", "--classical", "DNE", "--basis", "dn4"],
        "ks-dne-parameters": ["estimate_ks_classical.py", "--classical", "DNE", "--basis", "dn4", "--parameter-permutations"],
        "ks-clavius": ["estimate_ks_classical.py", "--classical", "Clavius", "--basis", "dn4"],
        "ks-clavius-parameters": ["estimate_ks_classical.py", "--classical", "Clavius", "--basis", "dn4", "--parameter-permutations"],
        "canonical-ve": ["canonical_ve.py"],
    }
    if args.experiment != "full-dn":
        v.require(args.dn4 is not None, "This experiment requires --dn4")
    env = os.environ.copy()
    env.update({
        "ZFC_BASELINE_SOURCE": str(args.baseline.resolve()),
        "ZFC_SOURCE_BUILDER": str(args.builder.resolve()),
        "ZFC_DAG230": str(args.dag.resolve()),
        "ZFC_EXPERIMENT_OUTPUT": str(args.output.resolve()),
        "PYTHONHASHSEED": "0",
    })
    if args.dn4:
        env["ZFC_DN4_SOURCE"] = str(args.dn4.resolve())
    selected = scripts[args.experiment]
    command = [sys.executable, "-B", str(Path(__file__).resolve().with_name(selected[0])), *selected[1:]]
    subprocess.run(command, env=env, check=True)


if __name__ == "__main__":
    main()
