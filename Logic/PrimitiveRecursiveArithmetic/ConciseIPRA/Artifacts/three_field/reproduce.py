"""Recompute the complete-module measurements and execute offline checks."""
from pathlib import Path
import argparse
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", action="store_true", help="also rebuild report.pdf")
    args = parser.parse_args()
    for script in ("measure.py", "tests/verify_three_field.py", "tests/verify_four_field.py"):
        subprocess.run([sys.executable, "-B", script], cwd=ROOT, check=True)
    triple = json.loads((ROOT / "evidence/three_field_validation.json").read_text())
    four = json.loads((ROOT / "evidence/compositions/verification.json").read_text())
    # Each suite raises on a mismatch; their full receipts are retained.
    result = {"three_field_cli_checks": triple["standalone_cli_checks"],
              "four_field_cli_checks": four["process_executions"],
              "canonical_compiler_round_trips": triple["canonical_round_trips"],
              "consumed_instructions": sum(triple["canonical_instruction_kinds"].values()),
              "failed_cli_checks": 0, "failed_round_trips": 0}
    result["total_cli_checks"] = result["three_field_cli_checks"] + result["four_field_cli_checks"]
    (ROOT / "evidence/reproduction.json").write_text(json.dumps(result, indent=2)+"\n")
    lines = [r"\begin{center}\small", r"\begin{tabular}{@{}lr@{}}", r"\toprule",
             r"Executed verification & Count\\", r"\midrule",
             f"Three-field isolated process checks & {result['three_field_cli_checks']}"+r"\\",
             f"Four-field isolated process checks & {result['four_field_cli_checks']}"+r"\\",
             f"All process checks & {result['total_cli_checks']}"+r"\\",
             f"Canonical compiler round trips & {result['canonical_compiler_round_trips']}"+r"\\",
             f"Consumed canonical instructions & {result['consumed_instructions']:,}"+r"\\",
             r"Unexpected verdicts or failed round trips & 0\\",
             r"\bottomrule", r"\end{tabular}", r"\end{center}"]
    (ROOT / "evidence/validation_summary.tex").write_text("\n".join(lines)+"\n")
    if args.pdf:
        subprocess.run(["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "report.tex"],
                       cwd=ROOT, check=True)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
