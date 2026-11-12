"""Reproduce finite evidence; the written proofs remain separate."""
from pathlib import Path
import argparse
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(relative):
    path = ROOT / relative
    result = subprocess.run([sys.executable, str(path)], cwd=path.parent,
                            text=True, capture_output=True)
    if result.returncode:
        sys.stdout.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise SystemExit(result.returncode)
    print("PASS", relative)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", action="store_true")
    args = parser.parse_args()
    run("checker/reproduce.py")
    run("mathematics/predecessor57.py")
    run("mathematics/block_macros.py")
    command = [sys.executable, str(ROOT / "build.py")]
    if args.pdf:
        command.append("--pdf")
    subprocess.run(command, cwd=ROOT, check=True)
    record = json.loads((ROOT / "checker/verification.json").read_text())
    print(json.dumps({"checker_executions": record["executions"],
                      "checker_failures": len(record["failures"]),
                      "status": "Finite checks passed; universal claims are written proofs."}))


if __name__ == "__main__":
    main()
