#!/usr/bin/env python3
"""Regenerate the standalone TeX, optionally compiling it with latexmk.

Run from any directory: python build_article.py --compile
Only local top-level \\input lines are expanded. No network is used.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
TARGET = ROOT / 'Alternating_Tails_and_Spectral_Defects.tex'


def expand(path: Path, stack: tuple[Path, ...] = ()) -> str:
    path = path.resolve()
    if path in stack or not path.is_relative_to(ROOT):
        raise ValueError('Cyclic or external TeX input: ' + str(path))
    source = path.read_text(encoding='utf-8')

    def include(match: re.Match[str]) -> str:
        child = (ROOT / match.group(1)).resolve()
        name = child.relative_to(ROOT).as_posix()
        body = expand(child, stack + (path,))
        return '% BEGIN INCLUDED SOURCE: ' + name + '\n' + body + '\n% END INCLUDED SOURCE: ' + name + '\n'

    return re.sub(r'^\\input\{([^}]+)\}[ \t]*$', include, source, flags=re.MULTILINE)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compile', action='store_true', help='Build the PDF with latexmk -pdf.')
    args = parser.parse_args()
    TARGET.write_text('% Standalone source generated from article.tex and the modular files.\n' + expand(ROOT / 'article.tex'), encoding='utf-8')
    print('Wrote ' + TARGET.name, flush=True)
    if args.compile:
        subprocess.run(['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error', TARGET.name], cwd=ROOT, check=True)


if __name__ == '__main__':
    main()

