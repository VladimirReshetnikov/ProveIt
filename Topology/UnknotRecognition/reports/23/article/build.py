#!/usr/bin/env python3
"""Build in isolation, settle references, and atomically publish a complete PDF."""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent
stem = "unknot_symbolic_compression"
with tempfile.TemporaryDirectory(prefix="proveit_article_") as directory:
    build = Path(directory)
    for source in root.glob("*.tex"):
        shutil.copy2(source, build / source.name)
    for name in ("tables", "figures"):
        shutil.copytree(root / name, build / name)
    for run in range(5):
        result = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                                 stem + ".tex"], cwd=build, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (root / f"build_pass_{run+1}.txt").write_text(result.stdout)
        if result.returncode:
            print(result.stdout[-8000:])
            raise SystemExit(result.returncode)
        log = (build / (stem + ".log")).read_text()
        needs_rerun = any(message in log for message in (
            "Rerun to get cross-references right", "Rerun to get outlines right",
            "Label(s) may have changed"))
        if run >= 1 and not needs_rerun:
            break
    else:
        raise SystemExit("LaTeX references did not stabilize after five passes")
    pdf = (build / (stem + ".pdf")).read_bytes()
    expected = re.search(r"\((\d+) pages?, (\d+) bytes\)", result.stdout)
    if not pdf.rstrip().endswith(b"%%EOF") or (expected and len(pdf) != int(expected.group(2))):
        raise SystemExit("Compiler output was incomplete; the published PDF was not replaced")
    for suffix, contents in ((".pdf", pdf), (".log", log.encode())):
        temporary = root / (stem + suffix + ".new")
        temporary.write_bytes(contents)
        temporary.replace(root / (stem + suffix))
print(root / (stem + ".pdf"))
