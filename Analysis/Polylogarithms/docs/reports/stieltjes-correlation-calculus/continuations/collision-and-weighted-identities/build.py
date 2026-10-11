#!/usr/bin/env python3
"""Build article.pdf and a single-file TeX source using standard pdfLaTeX.

No shell escape, downloads, BibTeX, or nonstandard fonts are needed.
Run from any working directory with: python build.py
"""
from pathlib import Path
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def flatten(path):
    text = path.read_text()
    def include(match):
        child = ROOT / match.group(1)
        if child.suffix != '.tex':
            child = child.with_suffix('.tex')
        return ('\n% BEGIN ' + str(child.relative_to(ROOT)) + '\n' +
                flatten(child) + '\n% END ' + str(child.relative_to(ROOT)) + '\n')
    return re.sub(r'\\input\{([^}]+)\}', include, text)


def main():
    if not shutil.which('pdflatex'):
        raise SystemExit('pdfLaTeX is required; install a standard TeX Live distribution.')
    build = ROOT / '_build'
    build.mkdir(exist_ok=True)
    for number in range(1, 4):
        command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                   '-halt-on-error', '-file-line-error', '-output-directory='+str(build),
                   'article.tex']
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        (build / f'pass_{number}.log').write_text(result.stdout+result.stderr)
        if result.returncode:
            raise SystemExit(f'TeX build failed in pass {number}; see _build/pass_{number}.log')
    log = (build / 'article.log').read_text(errors='replace')
    problems = [line for line in log.splitlines() if
                'undefined' in line or 'multiply defined' in line or
                'Overfull' in line or 'Token not allowed' in line]
    if problems:
        raise SystemExit('Unresolved TeX quality issues:\n'+'\n'.join(problems))
    shutil.copy2(build/'article.pdf', ROOT/'article.pdf')
    standalone = '% Generated from the modular source by build.py; edit the modular files.\n'+flatten(ROOT/'article.tex')
    (ROOT/'article_standalone.tex').write_text(standalone)
    result = {'status':'passed','passes':3,'undefined_references':False,
              'overfull_boxes':False,'standalone_source':'article_standalone.tex',
              'pdf_bytes':(ROOT/'article.pdf').stat().st_size}
    (ROOT/'results/build_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
