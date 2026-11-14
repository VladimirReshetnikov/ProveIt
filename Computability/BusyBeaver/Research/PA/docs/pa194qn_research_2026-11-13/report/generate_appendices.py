#!/usr/bin/env python3
"""Generate the complete table and comparison appendices from delivered data."""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def tex(text):
    out = str(text).replace('`', '')
    table = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%', '$': r'\$',
             '#': r'\#', '_': r'\_', '{': r'\{', '}': r'\}', '~': r'\textasciitilde{}',
             '^': r'\textasciicircum{}', 'Γ': r'$\Gamma$', '→': r'$\to$',
             '≤': r'$\le$', '≥': r'$\ge$', '—': '---', '–': '--'}
    return ''.join(table.get(c, c) for c in out)


def machine_table():
    rows = {}
    for line in (ROOT / 'machine/machine.tm').read_text().splitlines():
        q, b, w, d, n = line.split()
        rows[int(q), int(b)] = f'{w}{d}{n}'
    assert set(rows) == {(q, b) for q in range(194) for b in (0, 1)}
    text = [r'{\small\ttfamily', r'\begin{longtable}{rll@{\hspace{0.7in}}rll}',
            r'\toprule $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\\midrule\endhead']
    for q in range(97):
        k = q + 97
        text.append(f'{q} & {rows[q,0]} & {rows[q,1]} & {k} & {rows[k,0]} & {rows[k,1]}'+r'\\')
    text += [r'\bottomrule\end{longtable}}']
    (HERE / 'transition_table.tex').write_text('\n'.join(text) + '\n')


def frontier():
    rows = json.loads((ROOT / 'comparison/frontier194.json').read_text())
    assert len(rows) == 34
    text = [r'{\small', r'\begin{longtable}{p{0.20\textwidth}p{0.15\textwidth}p{0.57\textwidth}}',
            r'\toprule Design & Evidence & Material change\\\midrule\endhead']
    for row in rows:
        status = ('Rejected' if 'rejected' in row['status'].lower() else
                  'Auxiliary' if 'auxiliary' in row['status'].lower() else 'Proof/physical')
        text.append(f"{tex(row['name'])} & {status} & {tex(row['change'])}" + r'\\[5pt]')
    text += [r'\bottomrule\end{longtable}}']
    (HERE / 'frontier.tex').write_text('\n'.join(text) + '\n')


def ledger():
    data = json.loads((ROOT / 'comparison/packet_ledger.json').read_text())
    rows = data if isinstance(data, list) else data['packets']
    assert len(rows) == 51
    text = [r'{\small', r'\begin{longtable}{p{0.34\textwidth}p{0.58\textwidth}}',
            r'\toprule Delivery & Contribution and status\\\midrule\endhead']
    for row in rows:
        summary = row['source_summary']
        if row.get('duplicate_note'):
            summary += ' ' + row['duplicate_note']
        name = r'\nolinkurl{' + row['packet'] + '}'
        if row['location'] == 'incoming':
            name += r'\newline\emph{Incoming ZIP}'
        text.append(name + ' & ' + tex(summary) + r'\\[7pt]')
    text += [r'\bottomrule\end{longtable}}']
    (HERE / 'packet_ledger.tex').write_text('\n'.join(text) + '\n')


if __name__ == '__main__':
    machine_table()
    frontier()
    ledger()
    print('Generated all 388 transitions, 34 frontier entries, and 51 packet entries.')
