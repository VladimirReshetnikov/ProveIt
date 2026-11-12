"""Reproduce the arithmetic, finite census, source metric and fixture checks."""
from pathlib import Path
import json
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def run(relative_script):
    p = subprocess.run([sys.executable, str(ROOT / relative_script)],
                       cwd=ROOT, capture_output=True, text=True, timeout=120)
    if p.returncode:
        raise RuntimeError(relative_script + "\n" + p.stdout + p.stderr)
    print(relative_script + ": passed")

def main():
    for script in ["code/predecessor46.py", "code/clock_minimum.py",
                   "code/checker_refinement/verify.py", "code/image_scope.py"]:
        run(script)
    destinations = {
        "code/predecessor46_results.json": "predecessor46_results.json",
        "code/clock_minimum_results.json": "clock_minimum_results.json",
        "code/checker_refinement/verification.json": "checker_verification.json",
        "code/image_scope_results.json": "image_scope_results.json",
    }
    for source, destination in destinations.items():
        shutil.copyfile(ROOT / source, ROOT / "evidence" / destination)
    a = json.loads((ROOT / "evidence/predecessor46_results.json").read_text())
    c = json.loads((ROOT / "evidence/checker_verification.json").read_text())
    summary = {"python": sys.version, "status": "all checks passed",
               "predecessor_nodes": a["nodes"]["predecessor"],
               "checker_measurements": c["measurements"],
               "fixture_executions": c["executions"],
               "failed_expectations": c["failed_expectations"],
               "limits": "Written mathematics; no new Lean/Rocq proof; full checker envelope not beaten"}
    (ROOT / "evidence/reproduction.json").write_text(
        json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))

if __name__ == "__main__":
    main()
