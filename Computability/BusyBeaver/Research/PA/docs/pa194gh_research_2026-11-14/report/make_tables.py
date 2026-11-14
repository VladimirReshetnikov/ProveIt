#!/usr/bin/env python3
"""Regenerate exact machine and verification tables from delivered artifacts."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
NAMES = ('PA194GH', 'PA194GHS')

def load(path):
    return json.loads(path.read_text())

def parse(path):
    data = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        key = int(q), int(b)
        assert key not in data and d in ('L', 'R')
        data[key] = int(w), d, int(n)
    assert set(data) == {(q, b) for q in range(194) for b in (0, 1)}
    assert {x[2] for x in data.values()} <= set(range(195))
    return data

def action(a):
    w, d, q = a
    return r'\texttt{' + str(w) + d + ('H' if q == 194 else str(q)) + '}'

tables = []
for name in NAMES:
    machine = ROOT / 'machines' / name
    rows = parse(machine / 'machine.tm')
    receipt = load(machine / 'receipt.json')
    assert hashlib.sha256((machine / 'machine.tm').read_bytes()).hexdigest() == receipt['dense_sha256']
    tables.extend([
        r'\subsection{' + name + '}',
        r'{\small',
        r'\begin{longtable}{@{}rll@{\qquad\quad}rll@{}}',
        r'\toprule $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\',
        r'\midrule\endhead',
    ])
    for q in range(97):
        cells = []
        for k in (q, q + 97):
            cells.extend([str(k), action(rows[k, 0]), action(rows[k, 1])])
        tables.append(' & '.join(cells) + r'\\')
    tables.extend([r'\bottomrule\end{longtable}', '}'])
(HERE / 'transition_tables.tex').write_text('\n'.join(tables) + '\n')

build = {name: load(ROOT / 'machines' / name / 'receipt.json') for name in NAMES}
independent = {name: load(ROOT / 'machines/PA194GH/independent/results' / name / 'receipt.json') for name in NAMES}
metrics = [
    ('Working controls / transition rows', ['194 / 388', '194 / 388']),
    ('Simultaneous fold cases', [str(4 * build[n]['folds']) for n in NAMES]),
    ('Primitive source sites', [f"{build[n]['source_sites']:,}" for n in NAMES]),
    ('Universal source outcomes', [f"{build[n]['source_outcomes']:,}" for n in NAMES]),
    ('Builder symbolic steps', [f"{build[n]['runtime']['total_steps']:,}" for n in NAMES]),
    ('Builder maximum per outcome', [str(build[n]['runtime']['max_steps']) for n in NAMES]),
    ('Independent symbolic steps', [f"{independent[n]['symbolic_steps']:,}" for n in NAMES]),
    ('Independent maximum per outcome', [str(independent[n]['maximum_symbolic_steps']) for n in NAMES]),
    ('Minimum positive duration constant', [str(independent[n]['minimum_positive_duration_constant']) for n in NAMES]),
    ('Literal list induction certificates', ['4', '4']),
    ('Exact blank-start transitions', [f"{independent[n]['startup_steps']:,}" for n in NAMES]),
]
text = [r'\begin{center}\small', r'\begin{tabular}{@{}lrr@{}}', r'\toprule Verified item & PA194GH & PA194GHS\\\midrule']
for label, values in metrics:
    text.append(label + ' & ' + ' & '.join(values) + r'\\')
text.extend([r'\bottomrule\end{tabular}', r'\end{center}',
    r'The independent checks rederive four unary-list sweep lemmas from the',
    r'actual tables and compare two source resolvers. Symbolic-step counts',
    r'count checker operations; they are not constant bounds on physical',
    r'execution with arbitrarily large registers. The duration certificates',
    r'give positive affine physical durations over the specified symbolic domain.',
    r'The detailed contracts, list lemmas, startup tapes and hashes are retained',
    r'under \file{machines/PA194GH/independent/results/}.'])
(HERE / 'verification_summary.tex').write_text('\n'.join(text) + '\n')
(HERE / 'facts.tex').write_text('% All exact displayed machine facts are generated from the delivered JSON receipts.\n')
print('Generated complete transition tables and verification summary for both machines.')
