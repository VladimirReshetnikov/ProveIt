#!/usr/bin/env python3
"""Build article.pdf and record a strict final-log audit; no network access.

Requires Python 3.9+ and a TeX distribution containing the packages named in
article.tex. Run from any directory: python path/to/code/build.py
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--engine', default='pdflatex', help='TeX executable (default: pdflatex)')
    parser.add_argument('--passes', type=int, default=3, help='Compilation passes, between 2 and 6')
    args = parser.parse_args()
    if not 2 <= args.passes <= 6:
        parser.error('--passes must be between 2 and 6')
    root = Path(__file__).resolve().parent.parent
    source = root / 'article.tex'
    if not source.is_file():
        raise FileNotFoundError(f'Missing source: {source}')
    engine = shutil.which(args.engine)
    if engine is None:
        raise RuntimeError(f'TeX engine not found: {args.engine}. Install a TeX distribution first.')
    data = root / 'data'
    data.mkdir(exist_ok=True)
    for number in range(1, args.passes + 1):
        result = subprocess.run(
            [engine, '-halt-on-error', '-interaction=nonstopmode', '-file-line-error', 'article.tex'],
            cwd=root, capture_output=True, text=True, errors='replace', check=False,
        )
        if result.returncode:
            failure = data / 'failed-build.txt'
            failure.write_text(result.stdout + '\n' + result.stderr, encoding='utf-8')
            raise RuntimeError(f'TeX pass {number} failed; see {failure}')
    log = (root / 'article.log').read_text(encoding='utf-8', errors='replace')
    warning_lines = [line.strip() for line in log.splitlines() if 'Warning:' in line]
    overfull = len(re.findall(r'Overfull \\[hv]box', log))
    underfull = len(re.findall(r'Underfull \\[hv]box', log))
    undefined = len(re.findall(r'(?:Reference|Citation) .*? undefined|There were undefined references', log))
    errors = [line for line in log.splitlines() if line.startswith('!')]
    page_match = re.search(r'Output written on article\.pdf \((\d+) pages?', log)
    report = {
        'status': 'PASS' if not (warning_lines or overfull or underfull or undefined or errors) else 'REVIEW',
        'engine': log.splitlines()[0],
        'passes': args.passes,
        'pages': int(page_match.group(1)) if page_match else None,
        'warnings': warning_lines,
        'overfull_boxes': overfull,
        'underfull_boxes': underfull,
        'undefined_references_or_citations': undefined,
        'errors': errors,
        'article_tex_sha256': digest(source),
        'article_pdf_sha256': digest(root / 'article.pdf'),
        'scope': 'Typesetting and final-log audit only; not a mathematical proof check.',
    }
    destination = data / 'build_report.json'
    destination.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))
    return 0 if report['status'] == 'PASS' else 2


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, subprocess.SubprocessError) as exc:
        print(f'Build failed: {exc}', file=sys.stderr)
        raise SystemExit(1)
