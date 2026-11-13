#!/usr/bin/env python3
"""Compare the seed-line Lean digit lists, exact TeX block and PDF text extraction."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

if sys.flags.optimize:
    raise SystemExit('Optimized Python is not accepted')
here = Path(__file__).resolve().parent
root = here.parents[1]
lean = here / 'SeedLines.lean'
tex = root / 'equation.tex'
pdf = root / 'equation.pdf'
seed = root / 'Lean/DiophantineConsistency/DecimalMachine215.lean'

def must(condition, message):
    if not condition:
        raise ValueError(message)

def hash_file(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def tex_lines(s):
    start = r'\begingroup\fontsize{7.7}{8.2}\selectfont\ttfamily' + '\n'
    must(s.count(start) == 1, 'ambiguous seed block')
    block = s.split(start, 1)[1].split(r'\endgroup', 1)[0]
    values = block.strip().splitlines()
    must(len(values) == 12 and all(re.fullmatch(r'[0-9]+\\par', v) for v in values), 'invalid TeX seed lines')
    return [v.removesuffix(r'\par') for v in values]

def lean_lines(s):
    block = s.split('def lines : List (List ℕ) := [\n', 1)[1].split('\n]\n', 1)[0]
    rows = block.splitlines()
    values = []
    for row in rows:
        match = re.fullmatch(r'  \[([0-9](?:, [0-9])*)\],?', row)
        must(match is not None, 'invalid Lean digit list')
        values.append(match.group(1).replace(', ', ''))
    must(len(values) == 12, 'wrong number of Lean rows')
    return values

def compare(a, b):
    must(a == b, 'digit lines differ')
    must(list(map(len, a)) == [62] * 11 + [33], 'wrong digit line lengths')
    must(len(''.join(a)) == 715, 'wrong overall seed length')
    must(a[6].startswith('0'), 'lost leading zero on line seven')

rows = tex_lines(tex.read_text())
lrows = lean_lines(lean.read_text())
compare(rows, lrows)
expected = re.search(r'^def seed : ℕ := ([0-9]+)$', seed.read_text(), re.M)
must(expected is not None and expected.group(1) == ''.join(rows), 'Lean seed numeral mismatch')
extracted = subprocess.run(['pdftotext', '-raw', str(pdf), '-'], check=True, capture_output=True).stdout.decode()
pdf_rows = [line.strip() for line in extracted.splitlines() if re.fullmatch(r'[0-9]{33}|[0-9]{62}', line.strip())]
compare(rows, pdf_rows)
for name, mutant in [('leading-zero', [*rows[:6], rows[6][1:], *rows[7:]]),
                     ('digit', [str((int(rows[0][0])+1)%10) + rows[0][1:], *rows[1:]]),
                     ('order', [rows[1], rows[0], *rows[2:]])]:
    try:
        compare(rows, mutant)
    except ValueError:
        continue
    raise RuntimeError('negative control not rejected: ' + name)
print(json.dumps({'status': 'PASS', 'line_lengths': list(map(len, rows)),
                  'digits': sum(map(len, rows)), 'leading_zero_line': 7,
                  'controls_rejected': ['leading-zero', 'digit', 'order'],
                  'inputs_sha256': {str(p.relative_to(root)): hash_file(p) for p in (lean, tex, pdf, seed)},
                  'pdf_extraction_sha256': hashlib.sha256(extracted.encode()).hexdigest()}, indent=2))
