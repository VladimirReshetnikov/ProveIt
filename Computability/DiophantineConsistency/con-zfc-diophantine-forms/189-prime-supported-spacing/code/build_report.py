#!/usr/bin/env python3
"""Build a self-contained TeX source and its PDF using standard pdflatex."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
NAME = 'ConZFC_Prime_Supported_Spacing'


def main():
    source = (ROOT / 'report/main.tex').read_text()
    for name in ['metrics.tex', 'residuals.tex']:
        source = source.replace('\\input{' + name + '}', (ROOT / 'report' / name).read_text())
    if '\\input{' in source:
        raise ValueError('Unexpanded TeX input')
    (ROOT / (NAME + '.tex')).write_text(source)
    with tempfile.TemporaryDirectory(prefix='prime-spacing-tex-') as tmp:
        directory = Path(tmp)
        tex = directory / (NAME + '.tex')
        tex.write_text(source)
        for _ in range(3):
            result = subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                                     '-halt-on-error', tex.name], cwd=directory,
                                    text=True, capture_output=True)
            if result.returncode:
                print(result.stdout[-8000:])
                raise RuntimeError('pdflatex failed')
        log = tex.with_suffix('.log').read_text(errors='replace')
        warnings = [line for line in log.splitlines()
                    if any(s in line for s in ['Overfull', 'undefined', 'LaTeX Warning'])]
        (ROOT / 'verification/latex_warnings.txt').write_text('\n'.join(warnings) + '\n')
        shutil.copyfile(tex.with_suffix('.pdf'), ROOT / (NAME + '.pdf'))
        receipt = {'status': 'PASS' if not warnings else 'WARNINGS',
                   'passes': 3, 'standalone_source': NAME + '.tex',
                   'pdf': NAME + '.pdf', 'warnings': warnings}
        (ROOT / 'verification/pdf_build.json').write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
