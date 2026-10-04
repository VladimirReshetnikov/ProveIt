#!/usr/bin/env python3
"""Regenerate the paper's coefficient appendix from the exact CSV data.

Python 3.9+, standard library only. Each printed degree-five/six coefficient is
also independently recomputed by the finite word-cut formula and by expansion
of the displayed nested brackets, including all coefficients that are zero.
"""
from __future__ import annotations
import csv
import json
from fractions import Fraction
from itertools import product, zip_longest
from pathlib import Path
from typing import Dict, List, Tuple
from verify_bch import cut_coefficient, page_terms

ROOT = Path(__file__).resolve().parent.parent
Row = Tuple[str, Fraction]


def load(name: str) -> Dict[int, List[Row]]:
    out: Dict[int, List[Row]] = {}
    with (ROOT / 'data' / name).open(encoding='utf-8', newline='') as f:
        for row in csv.DictReader(f):
            n = int(row['degree'])
            c = Fraction(int(row['numerator']), int(row['denominator']))
            out.setdefault(n, []).append((row['word'], c))
    return out


def frac(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    sign = '-' if q < 0 else ''
    return sign + r'\frac{' + str(abs(q.numerator)) + '}{' + str(q.denominator) + '}'


def word(w: str) -> str:
    return r'$\mathrm{' + w + '}$'


def pair_table(rows1: List[Row], rows2: List[Row], title1: str, title2: str,
               caption: str, label: str, certificate: bool = False) -> str:
    columns = '@{}lrr@{\\hspace{2.2em}}lrr@{}' if certificate else '@{}lr@{\\hspace{3em}}lr@{}'
    span = 3 if certificate else 2
    total = 2 * span
    head = (r'\multicolumn{' + str(span) + '}{c}{' + title1 + '} & ' +
            r'\multicolumn{' + str(span) + '}{c}{' + title2 + r'} \\' + '\n')
    cols = r'$w$ & $c_{\rm cut}$ & $c_{\rm bracket}$ & $w$ & $c_{\rm cut}$ & $c_{\rm bracket}$ \\' if certificate else r'$w$ & coefficient of $L(w)$ & $w$ & coefficient of $L(w)$ \\'
    text = [r'\begingroup\small', r'\renewcommand{\arraystretch}{1.45}',
            r'\begin{longtable}{' + columns + '}',
            r'\caption{' + caption + r'}\label{' + label + r'}\\',
            r'\toprule', head, cols, r'\midrule\endfirsthead',
            r'\multicolumn{' + str(total) + r'}{c}{\tablename\ \thetable\ (continued)}\\',
            r'\toprule', head, cols, r'\midrule\endhead',
            r'\bottomrule\endfoot']
    for a, b in zip_longest(rows1, rows2):
        parts = []
        for entry in (a, b):
            if entry is None:
                parts.extend(['--'] * span)
            else:
                w, c = entry
                parts.append(word(w))
                parts.append('$' + frac(c) + '$')
                if certificate:
                    parts.append('$' + frac(c) + '$')
        text.append(' & '.join(parts) + r' \\')
    text.extend([r'\end{longtable}', r'\endgroup'])
    return '\n'.join(text) + '\n'


def main() -> None:
    assoc = load('bch_associative.csv')
    bch = load('bch_lyndon.csv')
    zass = load('zassenhaus_lyndon.csv')
    report = json.loads((ROOT / 'data' / 'verification_report.json').read_text(encoding='utf-8'))
    if report['table_degree'] < 8:
        raise ValueError('Regenerate the data through at least degree 8 before making the appendix.')
    displayed = page_terms()
    for n in (5, 6):
        known = dict(assoc[n])
        for letters in product('XY', repeat=n):
            w = ''.join(letters)
            c = cut_coefficient(w)
            if c != known.get(w, Fraction(0)) or c != displayed[n].get(w, Fraction(0)):
                raise AssertionError(f'Certificate mismatch at {w}')
    text = [r'''\section{Coefficient certificates and additional complete degrees}\label{sec:tables}
\subsection{All nonzero associative coefficients in degrees five and six}
Table~\ref{tab:certificate56} is a finite certificate for \cref{eq:Z5,eq:Z6}.
Its two coefficient columns on each side come from the cut formula
\cref{eq:word-cut} and expansion of the displayed right-nested brackets,
respectively. Both calculations give zero on every word absent from the table.
For degree five these are only $XXXXX$ and $YYYYY$; for degree six all $64$ possible
words, including the $36$ zero coefficients, are compared by the accompanying
script. Thus equality is checked in the free associative algebra, not in a
matrix quotient that might hide a Lie identity.
''']
    text.append(pair_table(assoc[5], assoc[6], '$Z_5$', '$Z_6$',
                          'Complete nonzero word-coefficient certificates for the displayed fifth and sixth degrees.',
                          'tab:certificate56', True))
    text.append(r'''\subsection{Complete seventh and eighth BCH degrees}
In the following table the entries specify exactly
$Z_n=\sum_w c_wL(w)$ for $n=7,8$, using \cref{eq:lyndon-definition};
there are no omitted nonzero terms in this convention. Expanding the brackets
and applying \cref{eq:word-cut} proves each identity by the same finite procedure
as in the preceding table. The CSV file continues these full expansions through
degree twelve.
''')
    text.append(pair_table(bch[7], bch[8], '$Z_7$', '$Z_8$',
                          'Additional complete BCH homogeneous polynomials in standard Lyndon bracketing.',
                          'tab:bch78'))
    text.append(r'''\subsection{Complete fifth and sixth Zassenhaus exponents}
These are the next two full exponents after the terms displayed on the source
page. A coefficient multiplies $L(w)$, not $R(w)$. Every entry follows either
from \cref{eq:zass-residual} or from \cref{eq:zass-finite-Lie}; the two constructions
agree exactly. Higher exponents through degree twelve are supplied as CSV data.
''')
    text.append(pair_table(zass[5], zass[6], '$C_5$', '$C_6$',
                          'Complete fifth and sixth Zassenhaus exponents.', 'tab:zass56'))
    text.append(r'''\subsection{Sizes of the exported expansions}
\begin{table}[htbp]
\centering\small
\begin{tabular}{@{}rrrr@{}}
\toprule
Degree & BCH words & BCH Lyndon entries & Zassenhaus Lyndon entries\\
\midrule
''')
    for row in report['counts']:
        text.append(f"{row['degree']} & {row['bch_nonzero_words']} & {row['bch_nonzero_lyndon']} & {row['zassenhaus_nonzero_lyndon']}" + r' \\')
    text.append(r'''\bottomrule
\end{tabular}
\caption{Numbers of nonzero coefficients in the supplied encodings. The degree-one Zassenhaus factor $e^Y$ is separated from the exponents $C_n$, $n\geq2$.}\label{tab:counts}
\end{table}
''')
    path = ROOT / 'tex' / 'appendix_tables.tex'
    path.write_text('\n'.join(text), encoding='utf-8')
    print(f'Wrote {path}; all degree-five/six certificate coefficients checked exactly.')


if __name__ == '__main__':
    main()
