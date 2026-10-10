#!/usr/bin/env python3
"""Compile the standalone article in an isolated temporary directory."""
from __future__ import annotations
import datetime, json, re, shutil, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def main() -> None:
    executable = shutil.which("pdflatex")
    if executable is None:
        raise SystemExit("pdflatex was not found. Install a TeX distribution with the packages listed in article.tex.")
    data = ROOT / "data"
    data.mkdir(exist_ok=True)
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    logs = []
    with tempfile.TemporaryDirectory(prefix="proveit-shifted-hurwitz-") as work:
        command = [executable, "-interaction=nonstopmode", "-halt-on-error",
                   f"-output-directory={work}", "article.tex"]
        for number in range(1, 4):
            try:
                run = subprocess.run(command, cwd=ROOT, capture_output=True,
                                     text=True, errors="replace", timeout=120)
            except subprocess.TimeoutExpired as exc:
                raise SystemExit(f"LaTeX pass {number} exceeded 120 seconds.") from exc
            logs.append(f"=== PASS {number} ===\n{run.stdout}\n{run.stderr}")
            if run.returncode != 0:
                (data / "build.log").write_text("\n".join(logs), encoding="utf-8")
                raise SystemExit(f"LaTeX pass {number} failed; inspect data/build.log.")
        final_log = (Path(work) / "article.log").read_text(encoding="utf-8", errors="replace")
        warnings = [line for line in final_log.splitlines()
                    if re.search(r"LaTeX Warning:|Package .* Warning:|Overfull|Underfull", line)]
        if "undefined references" in final_log or "undefined citations" in final_log:
            raise SystemExit("The last LaTeX pass contains unresolved references.")
        shutil.copy2(Path(work) / "article.pdf", ROOT / "article.pdf")
    pages = re.search(r"\((\d+) pages,", final_log)
    (data / "build.log").write_text("\n".join(logs), encoding="utf-8")
    report = {"status": "compiled", "passes": 3, "started_utc": started,
              "pages": int(pages.group(1)) if pages else None,
              "final_pass_warnings": warnings,
              "byte_reproducibility": "Not asserted: PDF metadata and run timestamps may change."}
    (data / "build_status.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    print(f"Wrote {ROOT / 'article.pdf'}")

if __name__ == "__main__":
    main()
