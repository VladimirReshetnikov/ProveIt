#!/usr/bin/env python3
"""Build the self-contained TeX source and PDF from the modular article."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
STEM = 'Differential_Polygamma_and_Lerch_Identities'


def flatten(path: Path) -> str:
    text = path.read_text()
    def replace(match):
        child = (ROOT / match.group(1)).with_suffix('.tex')
        return '\n% BEGIN ' + child.relative_to(ROOT).as_posix() + '\n' + flatten(child) + '\n% END ' + child.relative_to(ROOT).as_posix() + '\n'
    return re.sub(r'\\input\{([^}]+)\}', replace, text)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--engine', default='pdflatex', choices=['pdflatex', 'lualatex'])
    parser.add_argument('--passes', default=3, type=int)
    parser.add_argument('--source-only', action='store_true')
    args = parser.parse_args()
    standalone = ROOT / (STEM + '.tex')
    standalone.write_text('% Generated from article.tex and sections/*.tex by build.py.\n' + flatten(ROOT / 'article.tex'))
    if args.source_only:
        print(standalone.name)
        return
    engine = shutil.which(args.engine)
    if not engine:
        raise SystemExit(f'{args.engine} is not installed.')
    build_dir = ROOT / '_build'
    build_dir.mkdir(exist_ok=True)
    started = time.time()
    for k in range(args.passes):
        result = subprocess.run([engine, '-interaction=nonstopmode', '-halt-on-error',
                                 '-file-line-error', '-output-directory=' + str(build_dir),
                                 standalone.name], cwd=ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (build_dir / f'pass_{k+1}.txt').write_text(result.stdout)
        if result.returncode:
            print(result.stdout[-9000:])
            raise SystemExit(result.returncode)
    log = (build_dir / (STEM + '.log')).read_text(errors='replace')
    pdf = ROOT / (STEM + '.pdf')
    shutil.copy2(build_dir / pdf.name, pdf)
    record = {
        'engine': args.engine,
        'engine_version': subprocess.check_output([engine, '--version'], text=True).splitlines()[0],
        'passes': args.passes, 'seconds': round(time.time() - started, 3),
        'source_sha256': hashlib.sha256(standalone.read_bytes()).hexdigest(),
        'pdf_sha256': hashlib.sha256(pdf.read_bytes()).hexdigest(),
        'overfull_boxes': len(re.findall(r'Overfull \\[hv]box', log)),
        'undefined_references': bool(re.search(r'undefined references|Reference .* undefined|Citation .* undefined', log)),
        'multiply_defined_labels': 'multiply defined' in log,
        'rendered_review': 'Recorded separately; compiling does not constitute visual review.'
    }
    try:
        import fitz
        with fitz.open(pdf) as document:
            record['pdf_pages'] = len(document)
    except ImportError:
        pass
    (ROOT / 'results').mkdir(exist_ok=True)
    (ROOT / 'results/build_record.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
