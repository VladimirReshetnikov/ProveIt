#!/usr/bin/env python3
"""Assemble the standalone TeX and build the complete article with latexmk."""
from pathlib import Path
import argparse
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
NAME = 'Higher_Reflection_Identities'
INPUT = re.compile(r'(?m)^\\input\{([^}]+)\}\s*$')


def expand(path, active=()):
    path = path.resolve()
    if path in active or not path.is_relative_to(ROOT):
        raise ValueError(f'Invalid or circular TeX input: {path}')
    source = path.read_text(encoding='utf-8')

    def include(match):
        child = ROOT / (match.group(1) + '.tex')
        return '% Begin ' + match.group(1) + '\n' + expand(child, active + (path,)) + '\n'

    return INPUT.sub(include, source)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tex-only', action='store_true')
    args = parser.parse_args()
    standalone = ROOT / (NAME + '.tex')
    standalone.write_text(expand(ROOT / 'article.tex'), encoding='utf-8')
    print('Wrote', standalone.name, flush=True)
    if args.tex_only:
        return
    if shutil.which('latexmk') is None:
        raise SystemExit('latexmk is required; alternatively compile the standalone TeX directly.')
    subprocess.run(['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error',
                    '-file-line-error', '-outdir=build', 'article.tex'], cwd=ROOT, check=True)
    shutil.copyfile(ROOT / 'build/article.pdf', ROOT / (NAME + '.pdf'))
    print('Wrote', NAME + '.pdf', flush=True)


if __name__ == '__main__':
    main()
