#!/usr/bin/env python3
"""Create a single TeX file from the authoritative modular article source."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
INPUT = re.compile(r"\\input\{([^}]+)\}")


def expand(path: Path, stack: tuple[Path, ...] = ()) -> str:
    path = path.resolve()
    if path in stack:
        raise ValueError(f"Recursive TeX input: {path}")
    if not path.is_relative_to(ROOT):
        raise ValueError(f"Input outside package: {path}")
    text = path.read_text(encoding="utf-8")
    def replace(match: re.Match[str]) -> str:
        child = ROOT / match.group(1)
        if not child.suffix:
            child = child.with_suffix(".tex")
        return f"\n% BEGIN {child.relative_to(ROOT)}\n" + expand(child, stack + (path,)) + f"\n% END {child.relative_to(ROOT)}\n"
    return INPUT.sub(replace, text)


if __name__ == "__main__":
    (ROOT / "standalone.tex").write_text(expand(ROOT / "article.tex"), encoding="utf-8")
    print("Wrote standalone.tex")
