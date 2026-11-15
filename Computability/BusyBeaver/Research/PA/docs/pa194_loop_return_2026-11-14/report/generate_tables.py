#!/usr/bin/env python3
"""Generate report tables from the finalized comparison and literal machines."""
from collections import Counter
from pathlib import Path
import csv
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'report'


def esc(value):
    substitutions = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%',
                     '$': r'\$', '#': r'\#', '_': r'\_', '{': r'\{',
                     '}': r'\}', '~': r'\textasciitilde{}', '^': r'\textasciicircum{}'}
    result = ''.join(substitutions.get(char, char) for char in str(value))
    for source, target in [('→', r'$\to$'), ('↔', r'$\leftrightarrow$'),
                           ('—', '---'), ('–', '--'), ('≤', r'$\le$')]:
        result = result.replace(source, target)
    return result


families = list(csv.DictReader((ROOT / 'comparison/families.csv').open()))
ids = {row['family']: index + 1 for index, row in enumerate(families)}
paragraph = r'>{\raggedright\arraybackslash}p'
lines = [r'\begingroup\small',
         r'\begin{longtable}{@{}' + paragraph + r'{0.06\linewidth}' +
         paragraph + r'{0.39\linewidth}' + paragraph + r'{0.49\linewidth}@{}}',
         r'\toprule No. & Family and named implementations & Recurring behavior and proof obligation\\\midrule\endhead']
for index, row in enumerate(families, 1):
    lines.append(str(index) + ' & ' + r'\textbf{' + esc(row['family']) + '}. ' +
                 esc(row['designs']) + ' & ' + esc(row['recurring_behavior']) +
                 ' ' + esc(row['proof_obligation']) + r'\\[5pt]')
lines += [r'\bottomrule\end{longtable}', r'\endgroup']
(OUT / 'family_table.tex').write_text('\n'.join(lines) + '\n')

named = list(csv.DictReader((ROOT / 'comparison/named_194_designs.csv').open()))
summary = json.loads((ROOT / 'comparison/summary.json').read_text())
named_summary = json.loads((ROOT / 'comparison/named_summary.json').read_text())


def delivery(row):
    # A historical locator may still contain docs/incoming after the packet
    # has been filed. Use the reconciled status at this exact snapshot.
    group = row['snapshot_group']
    if group == 'current incoming new design':
        return 'Incoming'
    if group.startswith('filed prior design;'):
        return 'Filed'
    raise ValueError('Unrecognized snapshot group: ' + group)


counts = Counter(delivery(row) for row in named)
if len(named) != summary['named_194_constructions']:
    raise ValueError('Named-design count differs from the final census')
if counts['Incoming'] != summary['new_principal_194_graphs_in_current_archives']:
    raise ValueError('Incoming-design count differs from the final census')
if counts['Filed'] != named_summary['inherited_named_prior_designs']:
    raise ValueError('Filed-design count differs from the named ledger')
if len(families) != named_summary['mechanism_families']:
    raise ValueError('Family count differs from the named ledger')

lines = [r'\begingroup\small',
         r'\begin{longtable}{@{}' + paragraph + r'{0.40\linewidth}r' +
         paragraph + r'{0.22\linewidth}r' + paragraph + r'{0.13\linewidth}@{}}',
         r'\toprule Name / consolidated aliases & Family & Byte digest prefix & Start & Delivery\\\midrule\endhead']
for row in sorted(named, key=lambda item: (ids[item['family']], item['name'])):
    digest = row['table_file_sha256'][:12]
    lines.append(esc(row['name']) + ' & ' + str(ids[row['family']]) + ' & ' +
                 r'\texttt{' + digest + '} & ' + esc(row['start']) + ' & ' +
                 delivery(row) + r'\\')
lines += [r'\bottomrule\end{longtable}', r'\endgroup']
(OUT / 'named_table.tex').write_text('\n'.join(lines) + '\n')


def parse(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q, b, w, move, target = line.split()
        key = int(q), int(b)
        if key in result:
            raise ValueError('Duplicate literal transition')
        result[key] = f'{w}{move}{target}'
    if set(result) != {(q, b) for q in range(194) for b in (0, 1)}:
        raise ValueError('The printed transition matrix is incomplete')
    return result


left = parse(ROOT / 'machines/PA194LCG/machine.tm')
right = parse(ROOT / 'machines/PA194LCGS/machine.tm')
lines = [r'\begingroup\small', r'\setlength{\tabcolsep}{14pt}',
         r'\begin{longtable}{rrrrr}',
         r'\toprule & \multicolumn{2}{c}{PA194LCG} & \multicolumn{2}{c}{PA194LCGS}\\',
         r'State & Read 0 & Read 1 & Read 0 & Read 1\\\midrule\endhead']
for q in range(194):
    cells = [left[q, 0], left[q, 1], right[q, 0], right[q, 1]]
    lines.append(str(q) + ' & ' + ' & '.join(r'\texttt{' + cell + '}' for cell in cells) + r'\\')
lines += [r'\bottomrule\end{longtable}', r'\endgroup']
(OUT / 'transition_tables.tex').write_text('\n'.join(lines) + '\n')
print(json.dumps({'families': len(families), 'named_designs': len(named),
                  'named_delivery_counts': dict(counts),
                  'literal_transition_rows_per_machine': len(left)}, indent=2))
