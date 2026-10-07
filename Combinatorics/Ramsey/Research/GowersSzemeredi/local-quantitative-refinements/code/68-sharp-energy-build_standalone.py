#!/usr/bin/env python3
"""Expand the article's section inputs into one conventional TeX source."""
from pathlib import Path
import re

base = Path(__file__).resolve().parents[1]
source = (base / "main.tex").read_text(encoding="utf-8")

def expand(match):
    rel = match.group(1) + ".tex"
    content = (base / rel).read_text(encoding="utf-8")
    return "\n% BEGIN " + rel + "\n" + content.rstrip() + "\n% END " + rel + "\n"

result = re.sub(r"\\input\{(sections/[^}]+)\}", expand, source)
if r"\input{sections/" in result:
    raise RuntimeError("An unexpanded section input remains")
dest = base / "gowers_sharp_energy_restriction.tex"
dest.write_text(result, encoding="utf-8")
print(dest)
