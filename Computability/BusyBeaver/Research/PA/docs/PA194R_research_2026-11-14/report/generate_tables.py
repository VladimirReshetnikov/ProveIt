#!/usr/bin/env python3
"""Regenerate report tables from the released artifacts (standard library)."""
from pathlib import Path
import csv
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def esc(s):
    replacements = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%',
                    '$': r'\$', '#': r'\#', '_': r'\_', '{': r'\{',
                    '}': r'\}', '~': r'\textasciitilde{}', '^': r'\textasciicircum{}'}
    return ''.join(replacements.get(c, c) for c in s.replace(chr(96), ''))


def transition_table():
    rows = {}
    for line in (ROOT / 'machines/PA194R/machine.tm').read_text().splitlines():
        q, b, w, d, t = line.split()
        rows[int(q), int(b)] = f'{w}{d}{t}'
    assert set(rows) == {(q, b) for q in range(194) for b in (0, 1)}
    out = [r'\begin{center}\footnotesize',
           r'\setlength{\tabcolsep}{4pt}',
           r'\renewcommand{\arraystretch}{1.04}',
           r'\begin{tabular}{@{}rll@{\hspace{1.6em}}rll@{\hspace{1.6em}}rll@{\hspace{1.6em}}rll@{}}',
           r'\toprule',
           ' & '.join([r'$q$', r'read 0', r'read 1'] * 4) + r'\\',
           r'\midrule']
    for i in range(49):
        cells = []
        for offset in (0, 49, 98, 147):
            q = i + offset
            cells.extend([str(q), r'\texttt{' + rows[q, 0] + '}',
                          r'\texttt{' + rows[q, 1] + '}'] if q < 194 else ['', '', ''])
        out.append(' & '.join(cells) + r'\\')
    out.extend([r'\bottomrule', r'\end{tabular}', r'\end{center}'])
    (HERE / 'transition_table.tex').write_text('\n'.join(out) + '\n')


def ledger():
    rows = list(csv.DictReader((ROOT / 'comparison/packet_ledger.csv').open()))
    assert len(rows) == 41
    out = [r'{\footnotesize',
           r'\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.37\linewidth}>{\raggedright\arraybackslash}p{0.59\linewidth}@{}}',
           r'\toprule Packet & Reported contribution\\\midrule\endfirsthead',
           r'\toprule Packet (continued) & Reported contribution\\\midrule\endhead',
           r'\midrule\multicolumn{2}{r}{Continued on next page}\\\endfoot',
           r'\bottomrule\endlastfoot']
    for i, row in enumerate(rows, 1):
        name = r'\textbf{' + str(i) + r'.} \nolinkurl{' + row['packet'] + '}'
        out.append(name + ' & ' + esc(row['reported_contribution']) + r'\\[5pt]')
    out.extend([r'\end{longtable}', '}'])
    (HERE / 'packet_ledger.tex').write_text('\n'.join(out) + '\n')


def verification():
    families = ('PA194R', 'PA194F', 'PA194A', 'PA194X')
    receipts = [json.loads((ROOT / 'verification/recorded' / f / 'receipt.json').read_text()) for f in families]
    built = [json.loads((ROOT / 'machines' / f / 'construction_receipt.json').read_text()) for f in families]
    lines = [
        ('Working states / rows', ['194 / 388'] * 4),
        ('Primitive source sites', [f"{r['source_sites']:,}" for r in receipts]),
        ('Universal outcomes', [f"{r['universal_source_outcomes']:,}" for r in receipts]),
        ('Construction symbolic steps', [f"{r['universal_contracts']['total_steps']:,}" for r in built]),
        ('Independent symbolic steps', [f"{r['symbolic_steps']:,}" for r in receipts]),
        ('Maximum independent steps/case', [str(r['maximum_symbolic_steps']) for r in receipts]),
        ('Minimum duration constant', [str(r['minimum_positive_duration_constant']) for r in receipts]),
        ('Blank startup transitions', [f"{r['startup_steps']:,}" for r in receipts]),
        ('Small zero-cut sites', ['4', '4', '149', '11']),
    ]
    out = [r'\begin{table}[ht]', r'\centering\small',
           r'\setlength{\tabcolsep}{5pt}', r'\begin{tabular}{@{}lrrrr@{}}', r'\toprule',
           'Check & ' + ' & '.join(families) + r'\\', r'\midrule']
    for name, values in lines:
        out.append(name + ' & ' + ' & '.join(values) + r'\\')
    out.extend([r'\bottomrule', r'\end{tabular}',
                r'\caption{Completed checks. Symbolic steps count checker operations, not actual run time for all numerical inputs.}',
                r'\end{table}'])
    (HERE / 'verification_table.tex').write_text('\n'.join(out) + '\n')


if __name__ == '__main__':
    transition_table()
    ledger()
    verification()
    print('Generated complete transition table, 41-packet ledger and verification table.')
