"""Assemble the standalone TeX and compile a fully cross-referenced PDF.

Run from any directory. The fragments are the editable source of record;
the assembled top-level TeX is also independently compilable.
"""
from pathlib import Path
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
NAME = "Higher_Digamma_Powers_and_Ordered_Gamma_Sums"
parts = ROOT / "tex_parts"
source = (parts / "core.tex").read_text(encoding="utf-8")
for marker, filename in (
    ("residue_polynomial.tex", "residue_polynomial.tex"),
    ("canonical_fifth.tex", "canonical_fifth.tex"),
    ("ordered_section.tex", "ordered_section.tex"),
    ("audit_section.tex", "audit_section.tex"),
    ("article_end.tex", "end.tex"),
):
    token = "% INSERT " + marker + " HERE"
    if source.count(token) != 1:
        raise RuntimeError("Expected one insertion marker: " + marker)
    source = source.replace(token, (parts / filename).read_text(encoding="utf-8"))
if "% INSERT " in source:
    raise RuntimeError("Unresolved insertion marker")
(ROOT / (NAME + ".tex")).write_text(source, encoding="utf-8")

if not shutil.which("pdflatex"):
    raise RuntimeError("pdflatex is required to build the PDF")
for run in range(3):
    result = subprocess.run(
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", NAME + ".tex"],
        cwd=ROOT, text=True, capture_output=True,
    )
    if result.returncode:
        print(result.stdout[-8000:])
        raise RuntimeError("pdflatex failed")
log = (ROOT / (NAME + ".log")).read_text(encoding="utf-8")
issues = [line for line in log.splitlines()
          if "Overfull" in line or "Warning:" in line
          or "undefined references" in line or "destination with the same" in line]
receipt = {
    "latex_exit_status": "pass",
    "passes": 3,
    "pdf_file": NAME + ".pdf",
    "source_file": NAME + ".tex",
    "warnings_or_overflows": issues,
    "underfull_boxes": len(re.findall(r"Underfull \\[hv]box", log)),
    "meaning": "Build diagnostics only; visual inspection is recorded separately.",
}
(ROOT / "validation").mkdir(exist_ok=True)
(ROOT / "validation" / "build_receipt.json").write_text(
    json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
print(json.dumps(receipt, indent=2))
if issues:
    raise RuntimeError("Review LaTeX warnings or overflows before delivery")
