#!/usr/bin/env python3
"""Build the modular article and emit its standalone TeX/PDF deliverables."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
STEM = 'Canonical_Digamma_and_Fifth_Moment'


def flatten(path):
    source = path.read_text(encoding='utf-8')
    def include(match):
        name = match.group(1)
        child = ROOT / (name if name.endswith('.tex') else name + '.tex')
        if not child.is_file():
            raise FileNotFoundError(child)
        return '% BEGIN ' + name + '\n' + flatten(child) + '\n% END ' + name + '\n'
    return re.sub(r'\\input\{([^}]+)\}', include, source)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-only', action='store_true')
    args = parser.parse_args()
    standalone = ROOT / (STEM + '.tex')
    standalone.write_text(flatten(ROOT / 'article.tex'), encoding='utf-8')
    if args.source_only:
        print(standalone.name)
        return
    build = ROOT / '_build'
    build.mkdir(exist_ok=True)
    if shutil.which('latexmk'):
        commands = [['latexmk', '-pdf', '-interaction=nonstopmode',
                     '-halt-on-error', '-outdir=' + str(build), 'article.tex']]
    else:
        if not shutil.which('pdflatex'):
            raise RuntimeError('Install TeX Live with pdflatex or latexmk.')
        commands = [['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                     '-output-directory=' + str(build), 'article.tex']] * 3
    logs = []
    for command in commands:
        done = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        logs.append(done.stdout + done.stderr)
        if done.returncode:
            (build / 'build_stdout.log').write_text('\n'.join(logs))
            raise RuntimeError('LaTeX failed; inspect _build/build_stdout.log.')
    (build / 'build_stdout.log').write_text('\n'.join(logs))
    transcript = (build / 'article.log').read_text(errors='replace')
    issues = re.findall(r'^.*(?:Overfull|Underfull|LaTeX Warning|Package .* Warning).*$',
                        transcript, flags=re.MULTILINE)
    if issues:
        raise RuntimeError('Resolve LaTeX layout/reference warnings:\n' + '\n'.join(issues))
    target = ROOT / (STEM + '.pdf')
    shutil.copyfile(build / 'article.pdf', target)
    pages = re.search(r'Output written on .*?\((\d+) pages?', transcript, re.DOTALL)
    report = {
        'source': 'article.tex', 'standalone_tex': standalone.name,
        'pdf': target.name, 'pages': int(pages.group(1)) if pages else None,
        'warnings': issues, 'sha256_pdf': hashlib.sha256(target.read_bytes()).hexdigest(),
        'sha256_standalone_tex': hashlib.sha256(standalone.read_bytes()).hexdigest(),
        'note': 'PDF bytes can vary between TeX engines or rebuild dates; mathematical source is authoritative.'
    }
    (ROOT / 'results').mkdir(exist_ok=True)
    (ROOT / 'results' / 'build_record.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
