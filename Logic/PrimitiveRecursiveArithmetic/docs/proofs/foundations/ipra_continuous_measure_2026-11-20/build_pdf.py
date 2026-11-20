#!/usr/bin/env python3
"""Build the report with installed pdfLaTeX and check its diagnostic log."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    paper = ROOT / 'paper'
    evidence = ROOT / 'validation'
    evidence.mkdir(exist_ok=True)
    env = dict(os.environ)
    # A local override from the caller is honored. Otherwise ask Kpathsea
    # whether the installed distribution has an actual usable format.
    found = subprocess.run(['kpsewhich', 'pdflatex.fmt'], text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    format_path = found.stdout.strip()
    if not format_path or not Path(format_path).is_file():
        local = ROOT / '.build' / 'texmf'
        setup = subprocess.run([sys.executable, str(ROOT / 'code' / 'prepare_tex_runtime.py'),
                                str(local)], text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, check=True)
        result = json.loads(setup.stdout)
        env.update(result['environment'])
    command = ['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'report.tex']
    runs = []
    for pass_number in range(1, 4):
        result = subprocess.run(command, cwd=paper, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (evidence / f'pdflatex_pass_{pass_number}.log').write_text(result.stdout)
        runs.append({'pass': pass_number, 'returncode': result.returncode})
        if result.returncode:
            print(result.stdout[-7000:])
            raise SystemExit(f'pdfLaTeX pass {pass_number} failed')
    log = (paper / 'report.log').read_text(errors='replace')
    problem_patterns = [r'Overfull \\[hv]box', r'LaTeX Warning:.*undefined',
                        r'There were undefined references', r'Missing character:',
                        r'Label .* multiply defined', r'pdfTeX warning.*duplicate']
    problems = [line for line in log.splitlines()
                if any(re.search(p, line) for p in problem_patterns)]
    pdf = paper / 'report.pdf'
    result = {'status': 'passed' if not problems else 'needs_layout_review',
              'engine': 'pdfLaTeX', 'runs': runs, 'diagnostics': problems,
              'pdf_bytes': pdf.stat().st_size,
              'sha256': hashlib.sha256(pdf.read_bytes()).hexdigest(),
              'visual_review': 'Required separately; this script does not inspect images.'}
    (evidence / 'pdf_build.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    if problems:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
