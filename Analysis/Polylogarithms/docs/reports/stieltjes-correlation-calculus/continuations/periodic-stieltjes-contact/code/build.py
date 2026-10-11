#!/usr/bin/env python3
"""Build the paper in isolation, retaining the PDF and a machine-readable receipt."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    executable = shutil.which("pdflatex")
    if executable is None:
        raise SystemExit("pdflatex was not found. Install a TeX distribution and retry.")
    sources = [ROOT / "article.tex", ROOT / "data" / "validation_summary.tex"]
    for source in sources:
        if not source.is_file():
            raise SystemExit(f"Missing required source: {source}")
    version = subprocess.run(
        [executable, "--version"], check=True, capture_output=True, text=True
    ).stdout.splitlines()[0]
    with tempfile.TemporaryDirectory(prefix="proveit-periodic-contact-") as name:
        work = Path(name)
        for source in sources:
            dest = work / source.relative_to(ROOT)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, dest)
        command = [executable, "-interaction=nonstopmode", "-halt-on-error",
                   "-file-line-error", "-no-shell-escape", "article.tex"]
        for number in range(1, 4):
            result = subprocess.run(command, cwd=work, text=True,
                                    capture_output=True, timeout=120)
            if result.returncode:
                failure = ROOT / "data" / "build_failure.log"
                failure.write_text(result.stdout + "\n" + result.stderr)
                raise SystemExit(f"LaTeX pass {number} failed; see {failure}.")
        log = (work / "article.log").read_text(errors="replace")
        fatal = ("There were undefined references", "There were undefined citations",
                 "Label(s) may have changed", "multiply defined")
        if any(message in log for message in fatal):
            (ROOT / "data" / "build_failure.log").write_text(log)
            raise SystemExit("Unresolved LaTeX cross-references; see data/build_failure.log.")
        pdf = work / "article.pdf"
        if not pdf.exists():
            raise SystemExit("LaTeX produced no PDF.")
        shutil.copy2(pdf, ROOT / "article.pdf")
        warnings = [line for line in log.splitlines()
                    if "Warning:" in line or "Overfull" in line]
        page_match = re.search(r"Output written on article\.pdf \((\d+) pages?", log)
        receipt = {
            "status": "PASS",
            "engine": version,
            "passes": 3,
            "page_count": int(page_match.group(1)) if page_match else None,
            "source_sha256": {str(p.relative_to(ROOT)): sha256(p) for p in sources},
            "pdf_sha256": sha256(ROOT / "article.pdf"),
            "pdf_bytes": (ROOT / "article.pdf").stat().st_size,
            "warnings": warnings,
            "note": "Compilation check only; visual review is recorded separately."
        }
        (ROOT / "data" / "build_receipt.json").write_text(
            json.dumps(receipt, indent=2) + "\n")
        # An explicit optional audit path remains outside the deliverable package.
        audit_log = os.environ.get("PROVEIT_BUILD_AUDIT_LOG")
        if audit_log:
            Path(audit_log).write_text(log)
        failure = ROOT / "data" / "build_failure.log"
        if failure.exists():
            failure.unlink()
        print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
