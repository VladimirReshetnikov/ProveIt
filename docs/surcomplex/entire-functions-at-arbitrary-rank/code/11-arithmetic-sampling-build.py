#!/usr/bin/env python3
"""Build the standalone article with three pdfLaTeX passes in a temporary directory."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Output PDF (default: beside this script)")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    source = root / "arithmetic_sampling.tex"
    output = (args.output or root / "arithmetic_sampling.pdf").resolve()
    executable = shutil.which("pdflatex")
    if executable is None:
        raise SystemExit("pdfLaTeX was not found. Install TeX Live or MiKTeX and add it to PATH.")
    if not source.is_file():
        raise SystemExit(f"Missing source: {source}")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="arithmetic-sampling-") as temp:
        work = Path(temp)
        for number in range(1, 4):
            result = subprocess.run(
                [executable, "-interaction=nonstopmode", "-halt-on-error", str(source)],
                cwd=work, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, encoding="utf-8", errors="replace", timeout=180,
            )
            if result.returncode:
                raise SystemExit(f"pdfLaTeX pass {number} failed:\n{result.stdout[-12000:]}")
        log = (work / "arithmetic_sampling.log").read_text(encoding="utf-8", errors="replace")
        warnings = [line.strip() for line in log.splitlines()
                    if re.search(r"^(?:LaTeX Warning:|Package .+ Warning:|(?:pdfTeX|LuaTeX) warning|Overfull|Underfull)", line)]
        unresolved = re.search(r"undefined references|Citation .* undefined|Reference .* undefined", log)
        if unresolved:
            raise SystemExit("Unresolved references remain after three passes.\n" + "\n".join(warnings))
        built = work / "arithmetic_sampling.pdf"
        if not built.is_file():
            raise SystemExit("pdfLaTeX finished without producing the expected PDF.")
        shutil.copy2(built, output)
        pages = re.search(r"Output written on .*?\((\d+) pages?", log, re.S)
        report = {
            "status": "PASS",
            "engine": "pdfLaTeX",
            "passes": 3,
            "pages": int(pages.group(1)) if pages else None,
            "source_file": source.name,
            "source_sha256": sha256(source),
            "pdf_file": output.name,
            "pdf_sha256": sha256(output),
            "diagnostics": warnings,
            "verification_scope": "PDF compilation only; not mathematical verification or visual inspection.",
        }
        (output.parent / "build_report.json").write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8"
        )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
