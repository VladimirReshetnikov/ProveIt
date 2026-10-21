#!/usr/bin/env python3
"""Replay the three independent formalism checks from any working directory.

Python 3 standard library only; no repository checkout or proof-search output
is required. The inherited native-calculus/ZFC calibration is not rechecked.
"""
import json
from pathlib import Path
import subprocess
import sys


def main():
    if not __debug__:
        raise RuntimeError("Assertions must be enabled; do not use python -O.")
    root = Path(__file__).resolve().parent

    def replay(relative_script, *relative_arguments):
        argv = [sys.executable, "-B", str(root / relative_script)]
        argv.extend(str(root / arg) for arg in relative_arguments)
        run = subprocess.run(argv, check=True, capture_output=True, text=True)
        return json.loads(run.stdout)

    seed = replay("seed/check_seed_reflexivity.py",
                  "seed/seed_reflexivity_proof.json")
    matrices = replay("matrices/check_restricted_L.py")
    source = replay("source_counterexample/check_local7_source.py")
    assert seed["status"] == "PASS"
    assert seed["closed_proof_nodes"] == 79 and seed["native_conclusion"] == 3
    assert matrices["status"] == "PASS" and len(matrices["matrices"]) == 2
    assert all(m["status"] == "PASS" for m in matrices["matrices"])
    assert source["status"] == "PASS_SOURCE_COUNTEREXAMPLE"
    assert source["after_wrong_MP"]["T"] == 1 and source["suffix_halts"]
    print(json.dumps({
        "status": "PASS",
        "checks": [
            {
                "name": "closed_native_seed_proof",
                "nodes": seed["closed_proof_nodes"],
                "native_conclusion": seed["native_conclusion"],
                "proof_sha256": seed["sha256"],
            },
            {
                "name": "restricted_L_logical_fragment_matrices",
                "models": [m["name"] for m in matrices["matrices"]],
                "gated_set_theoretic_bundle": "EXCLUDED; each matrix explicitly fails a permitted instance",
            },
            {
                "name": "local7_source_macro_counterexample",
                "spurious_MP_output": source["after_wrong_MP"]["T"],
                "halting_suffix": source["suffix_halts"],
            },
        ],
        "scope": "Finite ordinary certificates. Inherited K/S derivability and macro contracts remain named premises. No physical binary refinement, new proof-assistant endpoint, or valid 217-state machine is claimed.",
    }, indent=2))


if __name__ == "__main__":
    main()
