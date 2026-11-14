#!/usr/bin/env python3
"""Generate the report's tables directly from the delivered artifacts."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'report'


def read(name):
    return json.loads((ROOT / name).read_text())


def esc(s):
    repl = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%',
            '$': r'\$', '#': r'\#', '_': r'\_', '{': r'\{',
            '}': r'\}', '~': r'\textasciitilde{}', '^': r'\textasciicircum{}'}
    return ''.join(repl.get(c, c) for c in str(s))


def prose(s):
    parts = str(s).split('`')
    return ''.join(esc(x) if i % 2 == 0 else r'\file{' + x + '}'
                   for i, x in enumerate(parts))


def row(xs):
    return ' & '.join(xs) + r'\\' + '\n'


def longtable(columns, heading, body, size=r'\small'):
    h = row(heading)
    return (size + '\n' + r'\begin{longtable}{' + columns + '}\n'
            + '\\toprule\n' + h + '\\midrule\\endfirsthead\n'
            + '\\toprule\n' + h + '\\midrule\\endhead\n'
            + '\\midrule\\multicolumn{' + str(len(heading))
            + r'}{r}{\emph{Continued on next page}}\\\endfoot' + '\n'
            + '\\bottomrule\\endlastfoot\n' + ''.join(body)
            + '\\end{longtable}\n\\normalsize\n')


def main():
    # Keep the standalone physical proof and its integrated version in sync.
    physical = (ROOT / 'proof/physical_ipra_audit.tex').read_text()
    body = physical.split(r'\begin{document}', 1)[1].split(r'\end{document}', 1)[0]
    body = body.replace(r'\maketitle', '').replace(r'\begin{abstract}', '').replace(r'\end{abstract}', '')
    body = re.sub(r'\\(sub)?section\{',
                  lambda m: r'\subsubsection{' if m.group(1) else r'\subsection{', body)
    macros = '\n'.join('\\providecommand{\\' + n + '}{\\operatorname{' + op + '}}'
                       for n, op in [('Run', 'Run'), ('enc', 'enc'), ('rev', 'rev'),
                                     ('Val', 'Val'), ('Valid', 'Valid')])
    (OUT / 'physical_bridge.tex').write_text(
        '% Generated from proof/physical_ipra_audit.tex; edit the standalone source.\n'
        + r'\section{A written iPRA bridge from literal machines to primitive source}' + '\n'
        + r'\label{sec:physical-ipra}' + '\n' + macros + '\n' + body)
    families = ('PA194AX11H', 'PA194QAX11H')
    receipts = [read(f'machines/{f}/independent/receipt.json') for f in families]
    assert all(r['status'] == 'PASS' for r in receipts)
    keys = [('Symbolic literal-engine operations', 'symbolic_steps'),
            ('Maximum operations in one contract', 'maximum_symbolic_steps'),
            ('Minimum positive duration constant', 'minimum_positive_duration_constant'),
            ('Generic list identities', 'generic_list_lemmas')]
    s = r'\begin{center}\begin{tabular}{lrr}' + '\n\\toprule\n'
    s += row(['Independent literal check', 'AX11H', 'QAX11H']) + '\\midrule\n'
    for name, k in keys:
        s += row([name] + [f"{r[k]:,}" for r in receipts])
    s += '\\bottomrule\n\\end{tabular}\\end{center}\n'
    (OUT / 'literal_results.tex').write_text(s)

    bodies = []
    for f in families:
        folds = read(f'machines/{f}/folds.json')
        for a, b, acts in folds:
            cells = [f, f'${a}\\mapsto {b}$']
            cells += [f"${w}{'R' if right else 'L'}{q}$" for w, right, q in acts]
            bodies.append(row(cells))
    (OUT / 'folds.tex').write_text(
        'The exact native fold pairs and replacement rows are:\n'
        + longtable('@{}llrr@{}', ['Family', 'Fold', 'Read 0', 'Read 1'], bodies))

    packets = read('comparison/delivery_ledger.json')['packets']
    assert len(packets) == 72
    bodies = []
    for i, p in enumerate(packets, 1):
        ident = r'\file{' + p['packet'] + '}'
        where = 'Incoming' if p['location'] == 'incoming' else 'Filed'
        ident += r'\newline ' + where + '; ' + esc(p.get('arrived', 'current at pinned snapshot'))
        bodies.append(row([str(i), ident, prose(p['reported_contribution'])]) + '\\addlinespace[3pt]\n')
    (OUT / 'delivery_ledger.tex').write_text(longtable(
        r'@{}r p{0.38\textwidth} p{0.53\textwidth}@{}',
        ['No.', 'Delivery / location', 'Reported contribution'], bodies))

    cats = {'reported principal construction': 'P', 'supplementary construction': 'S',
            'source-validated research rotation': 'V', 'research auxiliary': 'A', 'rejected': 'R'}
    frontier = sorted(read('comparison/frontier194.json')['classes'], key=lambda x: (x['evidence_category'], x['name'].lower()))
    assert len(frontier) == 82
    bodies = []
    for i, p in enumerate(frontier, 1):
        name = prose(p['name']) + r'\newline {\ttfamily\footnotesize ' + p['graph_hash'][:16] + '}'
        bodies.append(row([str(i), name, cats[p['evidence_category']], prose(p['mechanism'])])
                      + ('\\addlinespace[3pt]\n' if i < len(frontier) else ''))
    (OUT / 'frontier_ledger.tex').write_text(longtable(
        r'@{}r p{0.29\textwidth} c p{0.54\textwidth}@{}',
        ['No.', 'Name / graph identifier', 'Class', 'Attributed mechanism'], bodies))

    tables = []
    for f in families:
        t = {}
        for line in (ROOT / f'machines/{f}/machine.tm').read_text().splitlines():
            q, b, w, d, n = line.split()
            t[int(q), int(b)] = (w, d, n)
        assert len(t) == 388 and set(q for q,b in t) == set(range(194))
        tables.append(t)
    bodies = []
    for q in range(194):
        cells = [str(q)]
        for t in tables:
            for b in (0, 1):
                w, d, n = t[q,b]
                cells.append(r'\texttt{' + f'{w}{d}{n}' + '}')
        bodies.append(row(cells))
        if q % 10 == 9 and q < 190:
            bodies.append('\\addlinespace[3pt]\n')
    (OUT / 'transition_tables.tex').write_text(longtable(
        '@{}r r r r r@{}', ['State', 'AX11H / 0', 'AX11H / 1', 'QAX11H / 0', 'QAX11H / 1'], bodies))
    print('Generated report tables from 72 deliveries, 82 graph classes, and both complete literal tables.')


if __name__ == '__main__':
    main()
