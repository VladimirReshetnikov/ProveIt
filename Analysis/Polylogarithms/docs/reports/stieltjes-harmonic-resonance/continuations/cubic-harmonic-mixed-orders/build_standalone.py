#!/usr/bin/env python3
"""Flatten this package's modular TeX into the delivered standalone source."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent


def expand(path, stack=()):
    path = path.resolve()
    if path in stack:
        raise ValueError(f"Recursive input: {path}")
    text = path.read_text(encoding="utf-8")

    def insert(match):
        child = (ROOT / (match.group(1) + ".tex")).resolve()
        child.relative_to(ROOT)
        name = child.relative_to(ROOT).as_posix()
        return (f"% BEGIN {name}\n" + expand(child, stack + (path,))
                + f"\n% END {name}\n")

    return re.sub(r"\\input\{([^}]+)\}", insert, text)


if __name__ == "__main__":
    target = ROOT / "Cubic_Tornheim_Harmonic_Stieltjes.tex"
    result = ("% Standalone source; generated from the modular article sources.\n"
              + expand(ROOT / "article.tex"))
    target.write_text(result, encoding="utf-8")
    print(f"Wrote {target.name} ({len(result.encode('utf-8'))} bytes)")
