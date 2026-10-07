#!/usr/bin/env python3
"""Assemble the complete, single-file TeX manuscript from editable sources."""
from pathlib import Path

root = Path(__file__).resolve().parents[1]
parts = ["frontmatter.tex", "sections/fourier.tex", "sections/rigidity.tex",
         "sections/interpolation.tex", "sections/norm_blocks.tex", "endmatter.tex"]
assembled = []
for name in parts:
    assembled.append("% BEGIN SOURCE: " + name + "\n")
    assembled.append((root / name).read_text(encoding="utf-8").rstrip() + "\n")
    assembled.append("% END SOURCE: " + name + "\n\n")
destination = root / "gowers_exact_local_profiles.tex"
destination.write_text("".join(assembled), encoding="utf-8")
print(destination.name)
