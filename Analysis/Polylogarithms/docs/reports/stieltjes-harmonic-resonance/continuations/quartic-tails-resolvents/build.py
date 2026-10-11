#!/usr/bin/env python3
"""Build the modular and self-contained article without external resources."""
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
NAME = 'Quartic_Tails_and_Complex_Resolvents'


def expand_source(path, stack=()):
    path = path.resolve()
    if path in stack:
        raise ValueError(f'Cyclic TeX input: {path}')
    if not path.is_relative_to(ROOT):
        raise ValueError(f'Input outside package: {path}')
    source = path.read_text(encoding='utf-8')
    pattern = re.compile(r'\\input\{([^}]+)\}')

    def replace(match):
        name = match.group(1)
        child = ROOT / name
        if not child.suffix:
            child = child.with_suffix('.tex')
        return (f'\n% BEGIN {child.relative_to(ROOT)}\n'
                + expand_source(child, stack + (path,))
                + f'\n% END {child.relative_to(ROOT)}\n')

    return pattern.sub(replace, source)


def main():
    standalone = ROOT / f'{NAME}.tex'
    standalone.write_text(expand_source(ROOT / 'article.tex'), encoding='utf-8')
    engine = shutil.which('pdflatex')
    if not engine:
        raise SystemExit('pdflatex is required. Standalone TeX was generated successfully.')
    build = ROOT / 'build'
    build.mkdir(exist_ok=True)
    command = [engine, '-interaction=nonstopmode', '-halt-on-error',
               '-file-line-error', f'-output-directory={build}',
               str(standalone)]
    for iteration in range(1, 4):
        result = subprocess.run(command, cwd=ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (build / f'pass-{iteration}.txt').write_text(result.stdout, encoding='utf-8')
        if result.returncode:
            print(result.stdout[-12000:])
            raise SystemExit(f'LaTeX pass {iteration} failed; see build/pass-{iteration}.txt')
    log = (build / f'{NAME}.log').read_text(encoding='utf-8', errors='replace')
    problems = [line for line in log.splitlines()
                if ('Overfull ' in line or 'undefined' in line.lower()
                    or 'multiply defined' in line.lower())]
    if problems:
        print('\n'.join(problems))
        raise SystemExit('Review the reported TeX issues before delivering the PDF.')
    destination = ROOT / f'{NAME}.pdf'
    shutil.copy2(build / f'{NAME}.pdf', destination)
    print(f'Built {destination.name}')
    print(f'Standalone source: {standalone.name}')


if __name__ == '__main__':
    main()

