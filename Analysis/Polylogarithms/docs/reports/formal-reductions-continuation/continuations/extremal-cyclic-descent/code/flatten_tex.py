#!/usr/bin/env python3
"""Create one complete text source; figures remain in the figures directory."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PATTERN = re.compile(r"\\input\{([^}]+)\}")


def expand(path, stack=()):
    path = path.resolve()
    if path in stack:
        raise ValueError(f"Cyclic input: {path}")
    text = path.read_text()
    def include(match):
        child = ROOT / match.group(1)
        if child.suffix != ".tex":
            child = child.with_suffix(".tex")
        return (f"% BEGIN included source: {child.relative_to(ROOT)}\n"
                + expand(child, (*stack, path))
                + f"\n% END included source: {child.relative_to(ROOT)}\n")
    return PATTERN.sub(include, text)


if __name__ == "__main__":
    out = ROOT / "article_single_source.tex"
    out.write_text("% Complete text source. Compile from the package root with figures/.\n"
                   + expand(ROOT / "article.tex"))
    print(out.name)
