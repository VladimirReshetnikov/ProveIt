"""Reproduce measurements, finite checks, and optionally the PDF offline."""
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", action="store_true")
    args = parser.parse_args()
    for script in ["measure.py", "verify.py", "code/universal_macro.py"]:
        subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=True)
    command = [sys.executable, str(ROOT / "build_report.py")]
    if args.pdf:
        command.append("--pdf")
    subprocess.run(command, cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
