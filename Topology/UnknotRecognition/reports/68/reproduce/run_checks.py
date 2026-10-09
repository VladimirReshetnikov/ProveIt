"""Run feature or full tests and independently replay the packaged witnesses."""
from pathlib import Path
import argparse
import json
import os
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="Run the entire maintained repository suite.")
    args = parser.parse_args()
    out = ROOT/"reproduced"
    out.mkdir(exist_ok=True)
    env = os.environ.copy()
    env["PYTHONPATH"] = str(ROOT/"fast") + (os.pathsep+env["PYTHONPATH"] if env.get("PYTHONPATH") else "")
    started = time.perf_counter()
    if args.full:
        commands = [[sys.executable,"-m","unittest","discover","-s","tests","-v"]]
    else:
        commands = [[sys.executable,"-m","unittest","discover","-s","tests","-p",name,"-v"]
                    for name in ("test_cocycle_transport*.py","test_normal_transport.py","test_marked_boundary.py")]
    logpath = out/("full_tests.log" if args.full else "feature_tests.log")
    with logpath.open("w") as log:
        for command in commands:
            print("Running:", " ".join(command), flush=True)
            run = subprocess.run(command,cwd=ROOT/"fast",env=env,stdout=log,stderr=subprocess.STDOUT)
            if run.returncode:
                print(logpath.read_text())
                raise SystemExit(run.returncode)
    subprocess.run([sys.executable,str(ROOT/"reproduce/verify_results.py")],
                   cwd=ROOT,env=env,check=True)
    peeled = ROOT/"reproduce/verify_peeled_monotonicity.py"
    if peeled.exists():
        subprocess.run([sys.executable,str(peeled),"--output",str(out/"peeled_monotonicity.json")],
                       cwd=ROOT,env=env,check=True)
    result = {"status":"PASS","mode":"full" if args.full else "features",
              "python":platform.python_version(),"elapsed_seconds":time.perf_counter()-started,
              "test_log":str(logpath.relative_to(ROOT)),
              "retained_replay":"reproduced/retained_proof_replay.json"}
    (out/"run_checks.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
    print("Optional Regina comparisons are reported as skipped by unittest when Regina is unavailable.")


if __name__ == "__main__":
    main()
