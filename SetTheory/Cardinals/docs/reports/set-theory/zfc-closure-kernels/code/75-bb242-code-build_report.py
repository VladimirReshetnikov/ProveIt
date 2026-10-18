#!/usr/bin/env python3
"""Regenerate the exact canonical transition appendix and compile report.pdf."""
from pathlib import Path
import argparse
import hashlib
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CANONICAL_SHA = '64ddeb2c01c3e9c7feffaffaad87266a270716c9307892a0445bf869b988984d'


def transition_appendix():
    data = (ROOT / 'machine/zfc242.tm').read_bytes()
    if hashlib.sha256(data).hexdigest() != CANONICAL_SHA:
        raise ValueError('Canonical table content identity differs.')
    rows = {}
    for line in data.decode('ascii').splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, move, target = line.split()
        rows[int(q), int(bit)] = (write, move, target)
    if set(rows) != {(q, b) for q in range(242) for b in (0, 1)}:
        raise ValueError('Expected exactly 242 complete binary states.')
    lines = [
        r'\begin{longtable}{rll@{\qquad}rll}',
        r'\toprule',
        r'State & Read 0 & Read 1 & State & Read 0 & Read 1\\',
        r'\midrule', r'\endfirsthead', r'\toprule',
        r'State & Read 0 & Read 1 & State & Read 0 & Read 1\\',
        r'\midrule', r'\endhead', r'\bottomrule', r'\endfoot',
    ]
    for q in range(121):
        cells = []
        for state in (q, q + 121):
            cells.append(str(state))
            for bit in (0, 1):
                write, move, target = rows[state, bit]
                cells.append('$' + r'\,'.join((write, move, target)) + '$')
        lines.append(' & '.join(cells) + r' \\')
    lines.append(r'\end{longtable}')
    (ROOT / 'transition-table.tex').write_text('\n'.join(lines) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table-only', action='store_true')
    args = parser.parse_args()
    transition_appendix()
    if args.table_only:
        print('Regenerated all 484 appendix transitions.')
        return
    executable = shutil.which('pdflatex')
    if executable is None:
        raise SystemExit('pdflatex is required; install a TeX Live distribution.')
    command = [executable, '-interaction=nonstopmode', '-halt-on-error', 'report.tex']
    for _ in range(3):
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        if result.returncode:
            print(result.stdout + result.stderr)
            raise SystemExit(result.returncode)
    log = (ROOT / 'report.log').read_text(errors='replace')
    bad = [line for line in log.splitlines()
           if 'Overfull' in line or 'undefined references' in line
           or 'undefined citations' in line or 'Rerun to get' in line]
    if bad:
        raise SystemExit('Report needs layout/reference review:\n' + '\n'.join(bad))
    print('Compiled report.pdf; all references resolved and no overfull boxes.')


if __name__ == '__main__':
    main()
