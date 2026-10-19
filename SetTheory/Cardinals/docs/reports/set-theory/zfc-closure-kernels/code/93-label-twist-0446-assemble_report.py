#!/usr/bin/env python3
"""Assemble the single-file LaTeX manuscript from its editable fragments."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
parts = sorted((ROOT / "report-parts").glob("*.tex"))
assert parts and parts[0].name == "00-prefix.tex"
assert parts[-1].name == "90-conclusion.tex"
body = "\n\n".join(
    "% ===== " + p.name + " =====\n" + p.read_text() for p in parts
)
body = re.sub(
    r"(?m)^\\input\{([^}]+)\}\s*$",
    lambda match: (ROOT / match.group(1)).read_text(),
    body,
)
assert body.count("\\begin{document}") == 1
assert body.count("\\end{document}") == 1
target = ROOT / "zfc_sub245_research.tex"
target.write_text(body + "\n")
print(f"Assembled {len(parts)} fragments into {target.name}")
