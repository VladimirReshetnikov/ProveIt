#!/usr/bin/env python3
"""Compile the article in isolation and record a reproducible build receipt.

Requires pdflatex plus the standard packages listed in article/article.tex.
The PDF is copied out only after three successful passes. No repository is edited.
"""
from __future__ import annotations
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    source = root / 'article' / 'article.tex'
    engine = shutil.which('pdflatex')
    if engine is None:
        raise SystemExit('pdflatex was not found; install a LaTeX distribution first.')
    if not source.is_file():
        raise SystemExit(f'Missing source: {source}')
    with tempfile.TemporaryDirectory(prefix='coincident-stieltjes-') as tmp:
        work = Path(tmp)
        shutil.copy2(source, work / source.name)
        for i in range(3):
            result = subprocess.run(
                [engine, '-interaction=nonstopmode', '-halt-on-error', source.name],
                cwd=work, capture_output=True, text=True, timeout=180,
            )
            if result.returncode:
                (root/'data'/'build_failure.log').write_text(result.stdout + result.stderr)
                raise SystemExit(f'LaTeX pass {i+1} failed; see data/build_failure.log.')
        log = (work/'article.log').read_text(errors='replace')
        if 'There were undefined references' in log or 'multiply-defined' in log:
            raise SystemExit('Unresolved references in final LaTeX pass.')
        overfull = re.findall(r'Overfull .*', log)
        if overfull:
            (root/'data'/'build_failure.log').write_text(log)
            raise SystemExit('Overfull boxes remain; see data/build_failure.log.')
        pdf = root/'article'/'article.pdf'
        shutil.copy2(work/'article.pdf', pdf)
        m = re.search(r'Output written on article.pdf \((\d+) pages?, (\d+) bytes\)', log)
        receipt = {
            'status': 'passed', 'engine': Path(engine).name, 'passes': 3,
            'page_count': int(m.group(1)) if m else None,
            'pdf_bytes': pdf.stat().st_size,
            'overfull_boxes': len(overfull), 'undefined_references': False,
            'source': 'article/article.tex', 'output': 'article/article.pdf',
            'note': 'Compilation receipt; rendered visual review is recorded separately.',
        }
        (root/'data'/'build_status.json').write_text(json.dumps(receipt, indent=2)+'\n')
        (root/'data'/'build.log').write_text(log)
        print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
