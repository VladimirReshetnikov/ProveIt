#!/usr/bin/env python3
"""Build the complete article with pdfLaTeX; keep temporary files outside it."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'report/report.pdf')
    args = parser.parse_args()
    executable = shutil.which('pdflatex')
    if executable is None:
        raise RuntimeError('Install pdfLaTeX with the packages listed in report/report.tex')
    check = subprocess.run([sys.executable, '-B', str(ROOT/'code/report_inputs.py'), '--check'],
                           capture_output=True, text=True)
    if check.returncode:
        raise RuntimeError(check.stdout + check.stderr)
    env = dict(os.environ, TZ='UTC', SOURCE_DATE_EPOCH='1792886400', FORCE_SOURCE_DATE='1')
    with tempfile.TemporaryDirectory(prefix='conzfc-report-') as directory:
        temporary = Path(directory)
        for source in (ROOT/'report').glob('*.tex'):
            shutil.copyfile(source, temporary/source.name)
        for _ in range(3):
            result = subprocess.run(
                [executable, '-interaction=nonstopmode', '-halt-on-error',
                 '-no-shell-escape', '-output-directory='+str(temporary), 'report.tex'],
                cwd=temporary, env=env, capture_output=True, text=True)
            if result.returncode:
                raise RuntimeError(result.stdout + result.stderr)
        log = (temporary/'report.log').read_text(errors='replace')
        bad = [line for line in log.splitlines()
               if ('Overfull ' in line or 'undefined' in line
                   or 'Rerun to get cross-references right' in line)]
        if bad:
            raise RuntimeError('Report layout or reference check failed:\n'+'\n'.join(bad))
        source = temporary/'report.pdf'
        args.output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, args.output)
        data = args.output.read_bytes()
        page_match = re.search(r'Output written on .*?\((\d+) pages,', log, flags=re.S)
        print(json.dumps({'status':'pass', 'output':str(args.output),
            'pages':int(page_match.group(1)) if page_match else None,
            'bytes':len(data), 'sha256':hashlib.sha256(data).hexdigest(),
            'passes':3, 'overfull_boxes':0, 'undefined_references':0}, indent=2))


if __name__ == '__main__':
    main()
