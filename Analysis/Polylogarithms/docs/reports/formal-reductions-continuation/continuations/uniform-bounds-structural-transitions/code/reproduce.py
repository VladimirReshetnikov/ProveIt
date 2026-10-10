#!/usr/bin/env python3
"""Replay exact certificates; optionally reproduce numerical diagnostics/figures."""
from pathlib import Path
import argparse
import json
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numerical",action="store_true",
                        help="also run the slower mpmath and SymPy diagnostics")
    parser.add_argument("--figures",action="store_true",
                        help="also regenerate the scientific plots")
    args=parser.parse_args()
    tasks = [
        ["code/verify_euler.py","--output","data/euler_exact_certificate.json"],
        ["code/verify_depth_orbits.py","--max-weight","10",
         "--output","data/depth_orbit_verification.json"],
        ["code/certify_radial_degeneracy.py"],
        ["code/certify_two_extrema.py"],
    ]
    if args.numerical:
        tasks += [
            ["code/check_weight7_identity_numeric.py"],
            ["code/axis_remainder_diagnostics.py"],
            ["code/verify_moderate_reflection.py","--dps","180",
             "--late-k","60","120","240","480","--half-N","24","48","96",
             "--output","data/moderate_reflection_checks.json"],
        ]
    if args.figures:
        tasks += [["code/plot_euler_bounds.py"],["code/plot_two_extrema.py"]]
    records=[]
    logdir=ROOT/"data"/"replay_logs"
    logdir.mkdir(parents=True,exist_ok=True)
    for task in tasks:
        started=time.monotonic()
        print("Running "+" ".join(task),flush=True)
        result=subprocess.run([sys.executable,*task],cwd=ROOT,text=True,
                              stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        name=Path(task[0]).stem
        (logdir/(name+".txt")).write_text(result.stdout)
        record={"script":task[0],"arguments":task[1:],
                "exit_code":result.returncode,
                "elapsed_seconds":round(time.monotonic()-started,3),
                "log":"data/replay_logs/"+name+".txt"}
        records.append(record)
        print(json.dumps(record),flush=True)
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)
    receipt={"status":"PASS","python":sys.version,"platform":platform.platform(),
             "exact_certificates":True,"numerical_diagnostics":args.numerical,
             "regenerated_figures":args.figures,"runs":records}
    (ROOT/"data"/"reproduction_receipt.json").write_text(
        json.dumps(receipt,indent=2)+"\n")
    print("All requested checks passed.",flush=True)


if __name__ == "__main__":
    main()
