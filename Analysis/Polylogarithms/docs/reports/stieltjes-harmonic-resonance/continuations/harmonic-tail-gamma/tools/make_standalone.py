#!/usr/bin/env python3
"""Assemble the modular article into an independently compilable TeX file."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
source = (ROOT / "article.tex").read_text()
pattern = re.compile(r"^\\input\{([^}]+)\}\s*$", re.MULTILINE)


def expand(match):
    name = match.group(1)
    path = ROOT / (name if name.endswith(".tex") else name + ".tex")
    content = path.read_text()
    return "% BEGIN " + str(path.relative_to(ROOT)) + "\n" + content + "\n% END " + name + "\n"


result, count = pattern.subn(expand, source)
if count != 9:
    raise RuntimeError(f"Expected nine section/reference inputs; found {count}")
if re.search(r"^\\input", result, re.MULTILINE):
    raise RuntimeError("Unexpected unexpanded input directive")
(ROOT / "standalone.tex").write_text(
    "% Complete article assembled from article.tex, sections/, and references.tex.\n"
    "% Edit the modular source and rerun tools/make_standalone.py to regenerate.\n"
    + result)
print("Created standalone.tex with all eight sections and the bibliography.")
