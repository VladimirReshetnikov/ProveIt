#!/usr/bin/env python3
"""Replay every finite certificate in this archive using Python 3.10+.

Run from any working directory. No external package or network is needed.
The general mathematical statements are proved in the papers, not by this
finite verification suite.
"""
import json
import platform
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"


def run(name, arguments=(), save_as=None):
    command = [sys.executable, str(ROOT / "code" / name), *arguments]
    process = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if process.returncode:
        raise RuntimeError(f"{name} failed:\n{process.stdout}\n{process.stderr}")
    data = json.loads(process.stdout)
    if save_as:
        (RESULTS / save_as).write_text(json.dumps(data, indent=2) + "\n")
    print(f"PASS {name}", flush=True)
    return data


def main():
    RESULTS.mkdir(exist_ok=True)
    sharp = run("verify_sharp_range.py")
    binary = run("check_binary_profile.py", save_as="check_binary_profile.json")
    general = run("independent_binomial_check.py", save_as="independent_binomial_check.json")
    torsion = run("verify_torsion_phase_transition.py")
    universal = run("universal_bound.py", ["--prime", "2", "--terms", "6"],
                    "universal_binary_six.json")
    profile = run("sparse_disk.py", ["--prime", "5", "--support",
                  "0,1,5,6,10,15,20,25,30", "--profile"], "nine_term_profile.json")
    assert sharp["status"] == "all exact checks passed"
    assert binary["all_checks_pass"] and general["all_match"]
    assert torsion["status"] == "all exact finite checks passed"
    assert universal["profiles"] == 84 and universal["maximum"] == 8
    assert profile == [
        {"left": "1/4", "right": "5/19", "maximum": 26},
        {"left": "5/19", "right": "4/15", "maximum": 25},
        {"left": "4/15", "right": "1/2", "maximum": 10},
        {"left": "1/2", "right": "infinity", "maximum": 8},
    ]
    report = {
        "status": "all archive checks passed",
        "python": platform.python_version(),
        "arithmetic": "exact integers, fractions and finite fields",
        "general_all_depth_cases": general["cases"],
        "sharp_range": sharp,
        "binary_polynomial_certificates": len(binary["witnesses"]),
        "torsion_greedy_capacity_cases": torsion["greedy_shell_capacity_cases"],
        "torsion_capped_average_cases": torsion["capped_root_average_cases"],
        "torsion_late_block_cases": torsion["late_block_constructions"],
        "torsion_small_packets": torsion["exhaustive_small_packets"],
        "universal_binary_six_profiles": universal["profiles"],
        "universal_binary_six_maximum": universal["maximum"],
        "nine_term_profile_verified": True,
        "scope": "Finite checks supplement the written proofs; they do not replace them.",
    }
    (RESULTS / "reproduction_summary.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
