#!/usr/bin/env python3
"""Build the self-contained TeX source and PDF, retaining a concise receipt."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
STEM = "Coincident_Stieltjes_and_Directional_Zeta"


def flatten(path, stack=()):
    path = path.resolve()
    if path in stack:
        raise ValueError(f"Recursive TeX input: {path}")
    content = path.read_text(encoding="utf-8")

    def replace(match):
        child = ROOT / match.group(1)
        if not child.suffix:
            child = child.with_suffix(".tex")
        return ("% BEGIN " + str(child.relative_to(ROOT)) + "\n"
                + flatten(child, stack + (path,))
                + "\n% END " + str(child.relative_to(ROOT)) + "\n")

    return re.sub(r"\\input\{([^}]+)\}", replace, content)


def main():
    source = ROOT / (STEM + ".tex")
    source.write_text(flatten(ROOT / "article.tex"), encoding="utf-8")
    records = []
    with tempfile.TemporaryDirectory(prefix="proveit-zeta-build-") as tmp:
        tmp = Path(tmp)
        # The isolated build sees only this one source: no input sections.
        shutil.copy2(source, tmp / source.name)
        for k in range(1, 4):
            command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                       source.name]
            result = subprocess.run(command, cwd=tmp, text=True,
                                    capture_output=True, check=False)
            records.append({"pass": k, "returncode": result.returncode})
            if result.returncode:
                raise RuntimeError(result.stdout[-7000:] + result.stderr[-2000:])
        log = (tmp / (STEM + ".log")).read_text(errors="replace")
        problems = [line for line in log.splitlines()
                    if any(x in line for x in [
                        "Overfull", "undefined", "multiply defined",
                        "destination with the same identifier",
                        "Fatal error", "Missing character"])]
        if problems:
            raise RuntimeError("\n".join(problems))
        pdf = ROOT / (STEM + ".pdf")
        shutil.copy2(tmp / pdf.name, pdf)
        (ROOT / "results" / "build_log.txt").write_text(log)
    receipt = {
        "build": "isolated single-source three-pass pdfLaTeX",
        "passes": records, "unresolved_layout_or_reference_problems": problems,
        "source": source.name, "pdf": pdf.name,
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "pdf_sha256": hashlib.sha256(pdf.read_bytes()).hexdigest(),
    }
    (ROOT / "results" / "build_status.json").write_text(
        json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
