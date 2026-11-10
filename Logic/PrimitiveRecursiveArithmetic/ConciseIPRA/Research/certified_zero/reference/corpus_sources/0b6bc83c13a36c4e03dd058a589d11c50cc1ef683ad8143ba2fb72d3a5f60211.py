"""Reproduce measurements and finite diagnostics; these do not replace the proof."""
import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", action="store_true",
                        help="also repeat the offline corpus and novelty scans")
    args = parser.parse_args()
    scripts = ["code/measure_checkers.py", "tests/verify.py",
               "tests/verify_ast_profile.py", "tests/verify_total_ast_profile.py",
               "code/numerical_diagnostics.py"]
    if args.corpus:
        scripts += ["code/audit_corpus.py", "code/audit_novelty.py"]
    for script in scripts:
        print("Running " + script, flush=True)
        subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=True)
    print("All requested reproduction steps passed.")


if __name__ == "__main__":
    main()
