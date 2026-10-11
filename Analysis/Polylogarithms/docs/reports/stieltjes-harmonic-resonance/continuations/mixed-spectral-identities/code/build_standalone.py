#!/usr/bin/env python3
"""Inline the modular article into its independently compilable TeX source."""
from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "ProveIt_Mixed_Spectral_Identities_2026-10-10.tex"
INPUT = re.compile(r"\\input\{([^}]+)\}")


def expand(path: Path, ancestors: tuple[Path, ...] = ()) -> str:
    path = path.resolve()
    if path in ancestors:
        raise ValueError(f"Recursive TeX input: {path}")
    if not path.is_relative_to(ROOT):
        raise ValueError(f"Input outside this package: {path}")
    source = path.read_text(encoding="utf-8")

    def replace(match: re.Match[str]) -> str:
        child = path.parent / match.group(1)
        if not child.suffix:
            child = child.with_suffix(".tex")
        label = child.relative_to(ROOT).as_posix()
        body = expand(child, ancestors + (path,))
        return f"% BEGIN INLINED SOURCE: {label}\n{body}\n% END INLINED SOURCE: {label}"

    return INPUT.sub(replace, source)


if __name__ == "__main__":
    text = (
        "% Standalone source generated from article.tex and its local inputs.\n"
        "% Regenerate with: python code/build_standalone.py\n"
        + expand(ROOT / "article.tex")
    )
    TARGET.write_text(text, encoding="utf-8")
    print(TARGET.name)
