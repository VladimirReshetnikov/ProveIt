"""Replay the portable frozen verification suites; optionally rebuild the PDF."""
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def run(relative):
    subprocess.run([sys.executable, str(ROOT / relative)], cwd=ROOT, check=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdf", action="store_true")
    parser.add_argument("--skip-manifest", action="store_true",
                        help="For deliberate edits after initial manifest verification.")
    args = parser.parse_args()
    if not args.skip_manifest:
        run("verify_manifest.py")
    run("measure.py")
    run("validation/verify_refinements.py")
    run("validation/verify_token_refinements.py")
    run("validation/verify_ast_refinement.py")
    run("compact_validation/verify477.py")
    run("assemble.py")
    if args.pdf:
        run("build_pdf.py")
    print("All requested reproduction steps passed.")

if __name__ == "__main__":
    main()

