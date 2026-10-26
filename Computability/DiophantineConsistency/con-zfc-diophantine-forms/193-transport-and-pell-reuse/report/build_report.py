#!/usr/bin/env python3
"""Assemble the standalone LaTeX and compile it, without shell escape."""
from pathlib import Path
import json
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent

def assemble(path, active=()):
    path = path.resolve()
    if path in active:
        raise ValueError("Cyclic TeX input")
    text = path.read_text()
    def replace(match):
        name = match.group(1)
        child = path.parent / name
        if child.suffix != ".tex":
            child = child.with_suffix(".tex")
        return "\n% BEGIN retained input: " + name + "\n" + \
            assemble(child, active + (path,)) + \
            "\n% END retained input: " + name + "\n"
    return re.sub(r"\\input\{([^}]+)\}", replace, text)

def main():
    single = assemble(ROOT / "main.tex")
    (ROOT / "report.tex").write_text(single)
    with tempfile.TemporaryDirectory(prefix="conzfc-report-") as temporary:
        for _ in range(3):
            done = subprocess.run(
                ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
                 "-halt-on-error", "-output-directory=" + temporary,
                 "report.tex"], cwd=ROOT, capture_output=True, text=True)
            if done.returncode:
                raise RuntimeError(done.stdout[-12000:] + done.stderr)
        log = (Path(temporary) / "report.log").read_text()
        fatal_diagnostics = [
            line for line in log.splitlines()
            if "Overfull" in line or "undefined" in line.lower()
            or "Label(s) may have changed" in line
        ]
        if fatal_diagnostics:
            raise ValueError("Report needs layout/reference repair:\n" +
                             "\n".join(fatal_diagnostics))
        shutil.copyfile(Path(temporary) / "report.pdf", ROOT / "report.pdf")
        print(json.dumps({"status": "PASS", "standalone_tex": "report/report.tex",
                          "pdf": "report/report.pdf",
                          "undefined_references": 0,
                          "overfull_boxes": 0,
                          "scope": "Compilation diagnostics; visual inspection is separate."},
                         indent=2))

if __name__ == "__main__":
    main()
