#!/usr/bin/env python3
"""Build the standalone article in a temporary directory; require convergence."""
from __future__ import annotations
import hashlib
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'article/real_order_threshold.tex'

def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> None:
    executable = shutil.which('pdflatex')
    if not executable:
        raise SystemExit('pdflatex is required; install a TeX distribution first.')
    with tempfile.TemporaryDirectory(prefix='proveit-realorder-') as tmp:
        work = Path(tmp)
        shutil.copy2(SOURCE, work / SOURCE.name)
        previous = None
        for pass_number in range(1, 6):
            proc = subprocess.run([executable, '-interaction=nonstopmode',
                                   '-halt-on-error', SOURCE.name], cwd=work,
                                  text=True, capture_output=True, timeout=120)
            if proc.returncode:
                raise SystemExit(proc.stdout[-10000:] + '\n' + proc.stderr)
            aux = b''.join((work / (SOURCE.stem + suffix)).read_bytes()
                           for suffix in ['.aux','.toc','.out']
                           if (work / (SOURCE.stem + suffix)).is_file())
            digest = hashlib.sha256(aux).hexdigest()
            if digest == previous and pass_number >= 3:
                break
            previous = digest
        else:
            raise SystemExit('Cross-references did not stabilize after five passes.')
        log = (work / (SOURCE.stem + '.log')).read_text(errors='replace')
        errors = [line for line in log.splitlines()
                  if 'Overfull' in line or 'undefined' in line.lower()
                  or 'Rerun to get' in line or 'Missing character' in line]
        if errors:
            raise SystemExit('Build did not pass checks:\n' + '\n'.join(errors))
        pdf = ROOT / 'article' / (SOURCE.stem + '.pdf')
        shutil.copy2(work / pdf.name, pdf)
        warnings = [line for line in log.splitlines() if 'Warning' in line or 'Underfull' in line]
        receipt = {'engine': subprocess.run([executable,'--version'],text=True,
                                          capture_output=True,check=True).stdout.splitlines()[0],
                   'passes': pass_number, 'cross_references_stable': True,
                   'layout_warnings': warnings, 'source_sha256': sha256(SOURCE),
                   'pdf_sha256': sha256(pdf),
                   'visual_review': 'Separate receipt; this script does not perform visual review.'}
        (ROOT/'data/build_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(receipt,indent=2))

if __name__ == '__main__':
    main()
