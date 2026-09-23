#!/usr/bin/env python3
"""Build the article without overwriting delivered files; optionally rerun checks."""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="run exact checks at q^128 precision")
    parser.add_argument("--output-dir", type=Path, default=Path("build"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    out = args.output_dir
    if not out.is_absolute():
        out = root / out
    out.mkdir(parents=True, exist_ok=True)
    tex = shutil.which("pdflatex")
    if tex is None:
        parser.error("pdflatex was not found. Install TeX Live or MiKTeX and add it to PATH.")
    for number in range(1, 4):
        command = [tex, "-interaction=nonstopmode", "-halt-on-error",
                   "-file-line-error", "-output-directory", str(out), str(root / "article.tex")]
        result = subprocess.run(command, cwd=root, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, errors="replace")
        log = out / f"latex-pass-{number}.txt"
        log.write_text(result.stdout, encoding="utf-8")
        if result.returncode:
            print(f"LaTeX pass {number} failed. See {log}", file=sys.stderr)
            print(result.stdout[-5000:], file=sys.stderr)
            return result.returncode
    text = (out / "article.log").read_text(encoding="utf-8", errors="replace")
    problems = [marker for marker in ("There were undefined references", "multiply defined",
                "Missing character:", "Overfull \\hbox", "Overfull \\vbox") if marker in text]
    if problems:
        print("LaTeX validation issues: " + ", ".join(problems), file=sys.stderr)
        return 1
    if args.verify:
        result = subprocess.run([sys.executable, str(root / "verify.py"),
                                 "--precision", "128", "--output", str(out / "verification.json")],
                                cwd=root)
        if result.returncode:
            return result.returncode
    report = {"status": "passed", "latex_passes": 3,
              "pdf": str(out / "article.pdf"), "exact_checks_requested": args.verify,
              "formal_verification": False}
    (out / "rebuild_report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Built {out / 'article.pdf'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
