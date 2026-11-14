#!/usr/bin/env python3
"""Regenerate the printed comparison and literal-machine appendices."""
from pathlib import Path
import csv

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def tex(text):
    replacements = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%',
                    '$': r'\$', '#': r'\#', '_': r'\_\allowbreak{}',
                    '{': r'\{', '}': r'\}', '~': r'\textasciitilde{}',
                    '^': r'\textasciicircum{}'}
    return ''.join(replacements.get(c, c) for c in text)

def rows(filename):
    with (ROOT / 'comparison' / filename).open(newline='') as handle:
        return list(csv.DictReader(handle))

def start_table(columns, heading):
    return [r'{\small\setlength{\tabcolsep}{5pt}',
            r'\renewcommand{\arraystretch}{1.08}',
            r'\begin{longtable}{@{}' + columns + r'@{}}',
            r'\toprule', heading + r'\\\midrule\endfirsthead',
            r'\toprule', heading + r'\\\midrule\endhead',
            r'\midrule\multicolumn{' + str(heading.count('&') + 1)
            + r'}{r}{\emph{Continued on next page}}\\\endfoot',
            r'\bottomrule\endlastfoot']

def finish_table(lines, filename):
    lines += [r'\end{longtable}', '}']
    (HERE / filename).write_text('\n'.join(lines) + '\n')

categories = {'supported packet construction': 'Principal',
              'supplementary construction': 'Supplementary',
              'research auxiliary': 'Auxiliary', 'research seed': 'Seed',
              'rejected': 'Rejected'}
ordering = {key: i for i, key in enumerate(categories)}
data = sorted(rows('frontier194.csv'), key=lambda r: (ordering[r['evidence_category']], r['name']))
lines = start_table(r'>{\raggedright\arraybackslash}p{0.22\linewidth}'
                    r'>{\raggedright\arraybackslash}p{0.15\linewidth}'
                    r'>{\raggedright\arraybackslash}p{0.53\linewidth}',
                    r'Name / graph identifier & Evidence & Mechanism or failure')
for r in data:
    lines.append(tex(r['name']) + r'\newline {\ttfamily\scriptsize '
                 + r['table_class_sha256'][:12] + '} & '
                 + categories[r['evidence_category']] + ' & '
                 + tex(r['mechanism']) + r'\\[5pt]')
finish_table(lines, 'frontier_table.tex')

data = rows('packet_ledger.csv')
lines = start_table(r'>{\raggedright\arraybackslash}p{0.34\linewidth}'
                    r'>{\raggedright\arraybackslash}p{0.60\linewidth}',
                    r'Packet identifier & Reported contribution and evidence scope')
for i, r in enumerate(data, 1):
    name = r['packet_id'].replace('filed:', '').replace('incoming:', 'Incoming: ')
    lines.append(str(i) + '. ' + tex(name) + ' & '
                 + tex(r['reported_contribution']) + r'\\[5pt]')
finish_table(lines, 'packet_table.tex')

table = {}
for line in (ROOT / 'machine/machine.tm').read_text().splitlines():
    q, b, w, direction, target = line.split()
    table[int(q), int(b)] = (int(w), direction, int(target))
assert len(table) == 388
def action(q, b):
    w, direction, target = table[q, b]
    return rf'${w}\mathrm{{{direction}}}{target}$'
lines = start_table('rrrrrrrrr',
                    r'State & Read 0 & Read 1 & State & Read 0 & Read 1 & State & Read 0 & Read 1')
for q in range(65):
    cells=[]
    for s in (q, q+65, q+130):
        cells += [str(s), action(s,0), action(s,1)] if s < 194 else ['', '', '']
    lines.append(' & '.join(cells) + r'\\')
finish_table(lines, 'transition_table.tex')
print('Generated 76-graph, 66-packet, and complete 194-state table appendices.')
