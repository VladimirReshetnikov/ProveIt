#!/usr/bin/env python3
"""Generate report tables from the delivered machine and audit receipts."""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def tex(value):
    text = str(value)
    text = text.replace('→', r'$\to$').replace('≤', r'$\le$').replace('−', '-')
    text = text.replace('Γ', r'$\Gamma$').replace('ρ', r'$\rho$')
    return ''.join({'&': r'\&', '%': r'\%', '#': r'\#', '_': r'\_',
                    '{': r'\{', '}': r'\}'}.get(c, c) for c in text)

families = ['4R', '5', '6']
data = {f: json.loads((ROOT / 'machines' / f / 'receipt.json').read_text()) for f in families}
identities = [r'\begin{center}\small', r'\begin{tabular}{@{}lll@{}}', r'\toprule',
              r'Machine & Construction & Dense-table SHA-256 \\\midrule']
for f in families:
    digest = data[f]['dense_sha256']
    label = '$M_{4R}$' if f == '4R' else f'$M_{f}$'
    desc = 'Source-preserving reassociation' if f == '4R' else f'Constructor coefficient {f}'
    identities.append(label + ' & ' + desc + r' & \begin{tabular}[t]{@{}l@{}}\ttfamily ' + digest[:32] +
                      r'\\\ttfamily ' + digest[32:] + r'\end{tabular}\\[4pt]')
identities += [r'\bottomrule\end{tabular}', r'\end{center}']
(HERE / 'identities.tex').write_text('\n'.join(identities) + '\n')

v = [r'\begin{center}\small', r'\begin{tabular}{@{}lrrr@{}}', r'\toprule',
     r'Checked quantity & $M_{4R}$ & $M_5$ & $M_6$ \\\midrule']
ind = {f: json.loads((ROOT / 'machines' / f / 'independent/receipt.json').read_text()) for f in families}
rows = [
    ('Working states / transition rows', ['194 / 388'] * 3),
    ('Resolved primitive sites', [data[f]['source_sites'] for f in families]),
    ('Universal source outcomes', [data[f]['source_contracts'] for f in families]),
    ('Construction symbolic steps', [data[f]['symbolic_validation']['total_steps'] for f in families]),
    ('Independent symbolic steps', [ind[f]['symbolic_steps'] for f in families]),
    ('Independent maximum per outcome', [ind[f]['maximum_symbolic_steps'] for f in families]),
    ('Minimum positive-duration constant', [ind[f]['minimum_positive_duration_constant'] for f in families]),
    ('Exact complete blank startup', [data[f]['startup']['steps'] for f in families]),
    ('Maximum source address length', [data[f]['source_maximum_path'] for f in families]),
    ('Simultaneous fold cases', [data[f]['local_cases'] for f in families]),
]
for name, values in rows:
    v.append(name + ' & ' + ' & '.join(f'{x:,}' if isinstance(x, int) else x for x in values) + r'\\')
v += [r'\bottomrule\end{tabular}', r'\end{center}',
      'Symbolic step counts measure checker operations, not physical Turing-machine running times. '
      'The startup counts are literal physical transitions.']
(HERE / 'validation.tex').write_text('\n'.join(v) + '\n')

t = {}
for line in (ROOT / 'machines/5/machine.native.tm').read_text().splitlines():
    q, b, w, d, n = line.split()
    t[int(q), int(b)] = (w, d, n)
states = sorted({q for q, b in t})
assert len(states) == 194
table = [r'\small\setlength{\tabcolsep}{14pt}', r'\begin{longtable}{@{}rcc@{}}',
         r'\toprule Control & Read 0 & Read 1\\\midrule\endfirsthead',
         r'\toprule Control & Read 0 & Read 1\\\midrule\endhead',
         r'\midrule\multicolumn{3}{r}{Continued on the next page}\\\endfoot',
         r'\bottomrule\endlastfoot']
for q in states:
    a = [r'$\act{' + w + '}{' + d + '}{' + n + '}$' for w, d, n in [t[q, 0], t[q, 1]]]
    table.append(f'{q} & {a[0]} & {a[1]}' + r'\\')
table += [r'\end{longtable}\normalsize']
(HERE / 'transition_table.tex').write_text('\n'.join(table) + '\n')

ledger = json.loads((ROOT / 'comparison/archive_ledger.json').read_text())['archives']
assert len(ledger) == 41
tab = [r'\footnotesize\setlength{\tabcolsep}{4pt}',
       r'\begin{longtable}{@{}p{0.34\linewidth}p{0.62\linewidth}@{}}',
       r'\toprule Packet & Contribution / comparison point\\\midrule\endfirsthead',
       r'\toprule Packet & Contribution / comparison point\\\midrule\endhead',
       r'\midrule\multicolumn{2}{r}{Continued on the next page}\\\endfoot',
       r'\bottomrule\endlastfoot']
for i, row in enumerate(ledger, 1):
    name = row['archive'].removesuffix('.zip')
    # Allow line breaks at underscores without treating labels as TeX commands.
    label = tex(name).replace(r'\_', r'\_\allowbreak ')
    tab.append(f'{i}. {label} & {tex(row["contribution"])}' + r'\\[5pt]')
tab += [r'\end{longtable}\normalsize']
(HERE / 'archive_ledger.tex').write_text('\n'.join(tab) + '\n')
print('Generated identities, validation, transition table, and 41-packet ledger.')
