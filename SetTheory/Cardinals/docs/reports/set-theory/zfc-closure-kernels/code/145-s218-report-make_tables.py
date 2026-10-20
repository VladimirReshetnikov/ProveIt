#!/usr/bin/env python3
"""Generate compact exact canonical-table appendices from machine data."""
from pathlib import Path

HERE = Path(__file__).resolve().parent


def render(name, target):
    rows = {}
    for line in (HERE.parent / 'machines' / name / 'canonical.tm').read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        rows[int(q), int(b)] = (int(w), d, int(z))
    assert set(rows) == {(q, b) for q in range(219) for b in (0, 1)}

    def action(q, b):
        w, d, z = rows[q, b]
        return f'{w}{d}' + ('H' if z == 219 else str(z))

    text = [r'\begin{center}', r'\setlength{\tabcolsep}{5pt}',
            r'\renewcommand{\arraystretch}{0.98}', r'\fontsize{7}{8}\selectfont',
            r'\begin{tabular}{rrr@{\hspace{12mm}}rrr@{\hspace{12mm}}rrr}',
            r'\toprule',
            r'$q$ & read 0 & read 1 & $q$ & read 0 & read 1 & $q$ & read 0 & read 1\\',
            r'\midrule']
    for i in range(73):
        cells = []
        for q in (i, i + 73, i + 146):
            cells.extend([str(q), r'\texttt{' + action(q, 0) + '}',
                          r'\texttt{' + action(q, 1) + '}'])
        text.append(' & '.join(cells) + r'\\')
    text.extend([r'\bottomrule', r'\end{tabular}', r'\end{center}'])
    (HERE / target).write_text('\n'.join(text) + '\n')


if __name__ == '__main__':
    render('rho6_219', 'rho6_table.tex')
    render('nop219', 'nop_table.tex')
