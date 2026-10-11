#!/usr/bin/env python3
"""Inline this package's local TeX inputs into one portable TeX source."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "Harmonic_Shift_Singularities_and_Exact_Moment_Identities.tex"
INPUT = re.compile(r"\\input\{([^}]+)\}")


def expand(path: Path, active: tuple[Path, ...] = ()) -> str:
    path = path.resolve()
    if path in active:
        raise ValueError(f"Cyclic TeX input: {path}")
    text = path.read_text(encoding="utf-8")

    def replace(match: re.Match[str]) -> str:
        child = ROOT / match.group(1)
        if not child.suffix:
            child = child.with_suffix(".tex")
        child = child.resolve()
        child.relative_to(ROOT)
        relative = child.relative_to(ROOT)
        return f"% BEGIN {relative}\n" + expand(child, active + (path,)) + f"\n% END {relative}\n"

    return INPUT.sub(replace, text)


if __name__ == "__main__":
    DESTINATION.write_text(
        "% Standalone source generated from the accompanying modular TeX.\n"
        "% Regenerate using python3 code/build_standalone.py.\n"
        + expand(ROOT / "article.tex"), encoding="utf-8",
    )
    print(DESTINATION.name)
