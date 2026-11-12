"""Reproduce the new term measurements and unchanged checker baselines.

The report's general mathematical result is a written equational proof.
Neither these finite experiments nor the baseline checks replace it.
"""
from pathlib import Path
import argparse
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PARTS = ("00_front.tex", "02_predecessor.tex", "03_lower_bound.tex",
         "04_bridge_and_evidence.tex")


def build_source():
    source = ROOT / "ipra_absorbing_predecessor.tex"
    source.write_text("\n".join((ROOT / "src" / p).read_text() for p in PARTS))
    return source


def compile_pdf(source):
    from pdf_build import build
    build(source, ROOT / "ipra_absorbing_predecessor.pdf",
          ROOT / "evidence/pdf_build.log")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", action="store_true", help="also rebuild the PDF")
    parser.add_argument("--source-only", action="store_true",
                        help="rebuild the flattened TeX, optionally its PDF")
    args = parser.parse_args()
    source = build_source()
    if not args.source_only:
        subprocess.run([sys.executable, str(ROOT / "code/predecessor50.py")],
                       cwd=ROOT, check=True)
        subprocess.run([sys.executable, str(ROOT / "baseline/verify_baselines.py")],
                       cwd=ROOT, check=True)
        arithmetic = json.loads((ROOT / "code/predecessor50_results.json").read_text())
        baseline = json.loads((ROOT / "baseline/verification.json").read_text())
        receipt = {
            "python": sys.version,
            "new_predecessor_nodes": arithmetic["term_nodes"]["absorbing_predecessor50"],
            "finite_arithmetic_identity_checks": arithmetic["fast_numerical_identity_checks"],
            "baseline_process_executions": baseline["executions"],
            "baseline_failures": len(baseline["failures"]),
            "new_checker_frontier_improvement": False,
            "proof_status": "Written internal equational proof; no new Lean/Rocq build.",
        }
        (ROOT / "evidence/reproduction.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(json.dumps(receipt, indent=2))
    if args.pdf:
        compile_pdf(source)
        print("PDF rebuilt successfully.")


if __name__ == "__main__":
    main()
