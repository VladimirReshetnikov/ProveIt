#!/usr/bin/env python3
"""Build the self-contained article with pdfLaTeX; run from any directory."""
from pathlib import Path
import argparse
import datetime as dt
import json
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
STEM = 'polylogarithms_resonance_correlations'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--engine', default='pdflatex')
    args = parser.parse_args()
    engine = shutil.which(args.engine)
    if engine is None:
        raise SystemExit('Install a TeX distribution with pdfLaTeX first.')
    # Keep intermediate passes away from the deliverable path. Readers
    # should only observe a complete PDF, never a partially written pass.
    with tempfile.TemporaryDirectory(prefix='proveit-tex-') as temp:
        staging = Path(temp)
        for pass_number in range(1, 4):
            proc = subprocess.run(
                [engine, '-interaction=nonstopmode', '-halt-on-error',
                 '-output-directory='+str(staging), STEM+'.tex'],
                cwd=ROOT, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
            )
            if proc.returncode:
                print(proc.stdout)
                raise SystemExit(proc.returncode)
            print('LaTeX pass', pass_number, 'completed.', flush=True)
        log = (staging/(STEM+'.log')).read_text(errors='replace')
        forbidden = ['Overfull \\hbox', 'Overfull \\vbox',
                     'There were undefined references', 'multiply defined',
                     'Missing character:', 'Undefined control sequence']
        problems = [token for token in forbidden if token in log]
        if problems:
            print(log)
            raise SystemExit('Inspect the LaTeX log: '+', '.join(problems))
        raw_pdf = (staging/(STEM+'.pdf')).read_bytes()
        if not raw_pdf.startswith(b'%PDF-') or b'%%EOF' not in raw_pdf[-128:]:
            raise SystemExit('The TeX output is not a complete PDF.')
        for suffix in ['pdf','log','aux','toc','out']:
            source = staging/(STEM+'.'+suffix)
            if source.exists():
                destination = ROOT/(STEM+'.'+suffix)
                temporary = destination.with_name(destination.name+'.tmp')
                shutil.copy2(source, temporary)
                os.replace(temporary, destination)
    version = subprocess.run([engine, '--version'], text=True,
                             stdout=subprocess.PIPE, check=True).stdout
    pdf = ROOT/(STEM+'.pdf')
    info = {'status': 'three passes; no unresolved references or overfull boxes',
            'engine': version.splitlines()[0],
            'built_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
            'pdf': pdf.name, 'bytes': pdf.stat().st_size}
    (ROOT/'data'/'build_info.json').write_text(json.dumps(info, indent=2)+'\n')
    print('Built', pdf)


if __name__ == '__main__':
    main()

