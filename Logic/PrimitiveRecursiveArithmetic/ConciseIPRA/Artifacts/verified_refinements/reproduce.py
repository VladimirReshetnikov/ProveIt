"""Run the three self-contained verifier suites and produce a compact receipt."""
from pathlib import Path
import argparse
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", action="store_true")
    args = parser.parse_args()
    suites = {}
    for name, expected in (("compact", 84), ("native", 144), ("strict", 224)):
        r = subprocess.run([sys.executable, "-B", str(ROOT/name/"verify.py")],
                           cwd=ROOT, text=True, capture_output=True)
        if r.returncode:
            print(r.stdout)
            print(r.stderr, file=sys.stderr)
            raise SystemExit(r.returncode)
        data = json.loads((ROOT/name/"verification.json").read_text())
        count = data.get("cli_checks", data.get("process_checks",
                         data.get("checks_run", data.get("executions"))))
        if count is None:
            count = len(data.get("checks", data.get("results", [])))
        failures = data.get("failures", 0)
        if isinstance(failures, list):
            failures = len(failures)
        if count != expected or failures:
            raise ValueError((name, count, expected, failures))
        suites[name] = dict(cli_checks=count, failures=failures,
                            metrics=data.get("metrics"))
        print(name + ": " + str(count) + " CLI checks passed")
    result = dict(suites=suites, total_cli_checks=sum(x["cli_checks"] for x in suites.values()),
                  failures=0, reference_python="3.12.14",
                  target_met=False,
                  limitation="Implementation refinements; no new axiom basis or all-coordinate compact record.")
    (ROOT/"evidence").mkdir(exist_ok=True)
    (ROOT/"evidence/reproduction.json").write_text(json.dumps(result, indent=2)+"\n")
    if args.pdf:
        subprocess.run([sys.executable, str(ROOT/"build_pdf.py")], cwd=ROOT, check=True)
    print(json.dumps({k:v for k,v in result.items() if k != "suites"}, indent=2))

if __name__ == "__main__":
    main()

