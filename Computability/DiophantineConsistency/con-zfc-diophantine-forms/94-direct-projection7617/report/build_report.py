#!/usr/bin/env python3
"""Rebuild the LaTeX PDF, keeping auxiliary files in a temporary directory."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent
name = "ConZFC_Direct_Projection"
with tempfile.TemporaryDirectory(prefix="con-zfc-paper-") as folder:
    for _ in range(3):
        result = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                                 "-output-directory=" + folder, name + ".tex"],
                                cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True)
        if result.returncode:
            raise RuntimeError(result.stdout[-8000:])
    warnings = [line for line in result.stdout.splitlines()
                if "Warning" in line or "Overfull" in line]
    if any("Overfull" in line or "undefined" in line.lower() for line in warnings):
        raise RuntimeError("Final PDF has unresolved layout/reference issues: " + repr(warnings))
    shutil.copy2(Path(folder) / (name + ".pdf"), root / (name + ".pdf"))
pages = re.search(r"\((\d+) pages?,", result.stdout.replace("\n", ""))
receipt = {"status": "PASS", "engine": "pdfLaTeX", "passes": 3,
           "pages": int(pages.group(1)) if pages else None,
           "final_pass_warnings": warnings,
           "source_sha256": hashlib.sha256((root / (name + ".tex")).read_bytes()).hexdigest(),
           "pdf_sha256": hashlib.sha256((root / (name + ".pdf")).read_bytes()).hexdigest()}
(root / "PDF_BUILD.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(root / (name + ".pdf"))
