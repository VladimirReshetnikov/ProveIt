#!/usr/bin/env python3
"""Regenerate the report's exact tables from the released JSON/TM evidence."""
from pathlib import Path
import csv
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def tex(s):
    repl = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%',
            '$': r'\$', '#': r'\#', '_': r'\_', '{': r'\{',
            '}': r'\}', '~': r'\textasciitilde{}', '^': r'\textasciicircum{}',
            'Γ': r'\ensuremath{\Gamma}', '→': r'\ensuremath{\to}',
            '−': r'\ensuremath{-}'}
    return ''.join(repl.get(c, c) for c in str(s))


def read_json(path):
    return json.loads((ROOT / path).read_text())


def action(row, halt=None):
    w, right, n = row
    return f'{w}{"R" if right else "L"}{"H" if n == halt else n}'


def folds():
    f = read_json('machines/PA194QN5/folds.json')
    assert f == read_json('machines/PA194QN6/folds.json')
    lines = [r'\begin{center}', r'\begin{tabular}{@{}rrll@{}}', r'\toprule',
             r'Removed & Retained & Read 0 & Read 1\\', r'\midrule']
    for removed, retained, rows in f:
        lines.append(f'{removed} & {retained} & {action(rows[0])} & {action(rows[1])}' + r'\\')
    lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
    (HERE / 'folds.tex').write_text('\n'.join(lines) + '\n')


def verification():
    names = ['PA194QN5', 'PA194QN6']
    construction = [read_json(f'machines/{n}/receipt.json') for n in names]
    independent = [read_json(f'evidence/independent/{n}/receipt.json') for n in names]
    assert all(x['runtime']['ok'] for x in construction)
    assert all(x['status'] == 'PASS' for x in independent)
    metrics = [
        ('Construction: all source outcomes', [x['runtime']['contracts'] for x in construction]),
        ('Construction: symbolic proof steps', [x['runtime']['total_steps'] for x in construction]),
        ('Construction: maximum per outcome', [x['runtime']['max_steps'] for x in construction]),
        ('Independent: all source outcomes', [x['source_outcomes'] for x in independent]),
        ('Independent: symbolic proof steps', [x['symbolic_steps'] for x in independent]),
        ('Independent: maximum per outcome', [x['maximum_symbolic_steps'] for x in independent]),
        ('Independent: positive-duration lower constant', [x['minimum_positive_duration_constant'] for x in independent]),
        ('List lemmas derived from literal rows', [x['list_lemmas_from_literal_table'] for x in independent]),
        ('Exact whole-tape blank startup', [x['startup_steps'] for x in independent]),
    ]
    lines = [r'\begin{center}', r'\begin{tabular}{@{}lrr@{}}', r'\toprule',
             r'Check & QN5 & QN6\\', r'\midrule']
    for label, values in metrics:
        lines.append(tex(label) + ' & ' + ' & '.join(f'{v:,}' for v in values) + r'\\')
    lines += [r'\midrule', r'All required checks & PASS & PASS\\',
              r'\bottomrule', r'\end{tabular}', r'\end{center}',
              r'Symbolic proof-step counts measure the checker trace, not a bound on the',
              r'number of literal transitions needed for arbitrary register values.',
              r'The startup row, in contrast, counts literal transitions from the blank tape.']
    (HERE / 'verification.tex').write_text('\n'.join(lines) + '\n')


def principal_table():
    rows = {}
    path = ROOT / 'machines/PA194QN5/machine.tm'
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        rows[int(q), int(b)] = (int(w), d == 'R', int(n))
    assert set(rows) == {(q, b) for q in range(194) for b in (0, 1)}
    lines = [r'\begingroup\small\setlength{\tabcolsep}{12pt}',
             r'\begin{longtable}{@{}rll@{\qquad}rll@{}}', r'\toprule',
             r'State & Read 0 & Read 1 & State & Read 0 & Read 1\\',
             r'\midrule\endhead',
             r'\bottomrule\endfoot']
    for q in range(97):
        values = []
        for s in (q, q + 97):
            values += [str(s), action(rows[s, 0], 194), action(rows[s, 1], 194)]
        lines.append(' & '.join(values) + r'\\')
        if q % 10 == 9 and q < 96:
            lines.append(r'\addlinespace[3pt]')
    lines += [r'\end{longtable}', r'\endgroup']
    (HERE / 'table_qn5.tex').write_text('\n'.join(lines) + '\n')


def packet_ledger():
    with (ROOT / 'comparison/packet_ledger66.csv').open(newline='') as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == 66
    lines = [r'\begingroup\small\setlength{\tabcolsep}{4pt}',
             r'\begin{longtable}{@{}p{0.04\linewidth}>{\raggedright\arraybackslash}p{0.34\linewidth}>{\raggedright\arraybackslash}p{0.56\linewidth}@{}}',
             r'\toprule', r'No. & Delivery & Comparison\\', r'\midrule\endhead',
             r'\bottomrule\endfoot']
    for row in rows:
        packet = row['packet']
        detail = row.get('comparison_detail') or row['reported_contribution']
        family = row.get('family', '')
        detail = (r'\textbf{' + tex(family) + '}. ' if family else '') + tex(detail)
        lines.append(tex(row['ordinal']) + r' & \file{' + packet + '} & ' + detail + r'\\')
        lines.append(r'\addlinespace[6pt]')
    lines += [r'\end{longtable}', r'\endgroup']
    (HERE / 'packet_ledger.tex').write_text('\n'.join(lines) + '\n')


if __name__ == '__main__':
    folds()
    verification()
    principal_table()
    packet_ledger()
    print('Generated folds, verification, complete principal table, and 66-delivery ledger.')
