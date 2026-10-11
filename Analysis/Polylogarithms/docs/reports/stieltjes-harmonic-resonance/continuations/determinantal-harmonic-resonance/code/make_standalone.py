#!/usr/bin/env python3
"""Flatten this package's local LaTeX inputs; no network or external files."""
from __future__ import annotations
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
INPUT = re.compile(r"\\input\{([^{}]+)\}")

def expand(path: pathlib.Path, active: tuple[pathlib.Path, ...] = ()) -> str:
    path = path.resolve()
    if ROOT not in path.parents:
        raise ValueError(f"Input escapes the package: {path}")
    if path in active:
        raise ValueError(f"Cyclic LaTeX input: {path}")
    text = path.read_text(encoding="utf-8")
    def replace(match: re.Match[str]) -> str:
        name = match.group(1)
        child = ROOT / (name if name.endswith(".tex") else name + ".tex")
        return (f"% BEGIN {name}\n" + expand(child, active + (path,))
                + f"\n% END {name}\n")
    return INPUT.sub(replace, text)

if __name__ == "__main__":
    target = ROOT / "article_standalone.tex"
    target.write_text(
        "% Generated from article.tex and its local inputs. Edit modular sources.\n"
        + expand(ROOT / "article.tex"), encoding="utf-8")
    print(f"Wrote {target.name}")
