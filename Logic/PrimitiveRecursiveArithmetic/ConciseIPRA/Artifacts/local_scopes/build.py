"""Compile the TeX report. Requires a LaTeX installation with latexmk."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    environment = os.environ.copy()
    environment['SOURCE_DATE_EPOCH'] = '1794268800'
    environment['FORCE_SOURCE_DATE'] = '1'
    with tempfile.TemporaryDirectory(prefix='ipra-tex-') as temporary:
        result = subprocess.run(
            ['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error',
             '-outdir=' + temporary, 'report.tex'],
            cwd=ROOT, env=environment, capture_output=True, text=True)
        (ROOT / 'evidence/build.log').write_text(result.stdout + result.stderr)
        log = Path(temporary) / 'report.log'
        if log.exists():
            shutil.copy2(log, ROOT / 'evidence/latex.log')
        if result.returncode:
            print((result.stdout + result.stderr)[-10000:])
            raise SystemExit(result.returncode)
        output = Path(temporary) / 'report.pdf'
        if not output.is_file():
            raise RuntimeError('LaTeX did not produce report.pdf')
        shutil.copy2(output, ROOT / 'report.pdf')
    print(json.dumps({'pdf': str(ROOT / 'report.pdf'),
                      'bytes': (ROOT / 'report.pdf').stat().st_size}))


if __name__ == '__main__':
    main()
