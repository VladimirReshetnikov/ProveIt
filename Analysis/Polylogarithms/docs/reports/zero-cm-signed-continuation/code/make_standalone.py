#!/usr/bin/env python3
"""Assemble one TeX source from the editorial section files.

The resulting TeX still uses the two figure PDFs in figures/. Keep that
folder alongside it when compiling, or use the complete ZIP package.
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
source = (ROOT / "article.tex").read_text()


def expand(match):
    relative = match.group(1)
    path = ROOT / (relative + ".tex")
    return ("\n% BEGIN INCLUDED SOURCE: " + relative + ".tex\n"
            + path.read_text()
            + "\n% END INCLUDED SOURCE: " + relative + ".tex\n")


source = re.sub(r"\\input\{([^}]+)\}", expand, source)
target = ROOT / "polylogarithms_saddles_and_zeros.tex"
target.write_text(source)
print(target.name)

