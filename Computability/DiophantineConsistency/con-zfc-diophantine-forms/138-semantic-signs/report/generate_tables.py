#!/usr/bin/env python3
"""Generate the literal principal residual appendix from its canonical JSON."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def term(coefficient, indices, first=False):
    sign = '-' if coefficient < 0 else ('' if first else '+')
    magnitude = abs(coefficient)
    factors = ''.join('z_{%d}' % i + ('^{%d}' % power if power > 1 else '')
                      for i, power in sorted(Counter(indices).items()))
    number = str(magnitude) if magnitude != 1 or not factors else ''
    return sign + number + factors

def contents():
    path = ROOT.parent / 'integer286/principal/centered/equation.json'
    raw = path.read_bytes()
    equation = json.loads(raw)
    if len(equation['variables']) != 286 or len(equation['residuals']) != 196:
        raise ValueError('Unexpected equation dimensions')
    out = ['% Generated from SHA-256 ' + hashlib.sha256(raw).hexdigest(),
           r'\begingroup\small',
           r'\setlength{\jot}{2pt}',
           r'\setlength{\abovedisplayskip}{3pt}',
           r'\setlength{\belowdisplayskip}{3pt}']
    for index, row in enumerate(equation['residuals']):
        pieces = [term(c, m, k == 0) for k, (c, m) in enumerate(row['terms'])]
        if any(len(m) > 2 for c, m in row['terms']):
            raise ValueError('Nonquadratic residual')
        chunks, chunk = [], []
        for piece in pieces:
            if chunk and (len(chunk) >= 5 or sum(map(len, chunk)) + len(piece) > 145):
                chunks.append(' '.join(chunk)); chunk = []
            chunk.append(piece)
        if chunk:
            chunks.append(' '.join(chunk))
        out.append(r'\begin{align*}')
        for k, chunk in enumerate(chunks):
            prefix = ('r_{%d}={}&' % index) if k == 0 else '&'
            suffix = r'\\' if k < len(chunks) - 1 else ''
            out.append(prefix + chunk + suffix)
        out.append(r'\end{align*}')
    out.append(r'\endgroup')
    return '\n'.join(out) + '\n'

def constants():
    raw = (ROOT.parent / 'positive10/inherited/indexed_constant_recipe.tex').read_text()
    start = raw.index(r'\textbf{The four fixed integers.}')
    stop = raw.index(r'\normalfont\fontsize{7.7}{8.2}\selectfont', start)
    body = raw[start:stop].replace(r'\fontsize{7.7}{8.2}', r'\fontsize{9}{10}')
    body = body.replace('is\n{\\fontsize{9}{10}\\selectfont\\ttfamily',
                        'is\\par\\noindent\n{\\fontsize{9}{10}\\selectfont\\ttfamily')
    preamble = r'''The following is the parent's complete finite constant recipe, retained
with its fixed indexed transition table. In this appendix the symbol $K$
means the constant $K_0$ in Section~\ref{sec:compact}; the local constant
$B$ is a numeral base, not the polynomial transport expression named $B$.
All indices and summation limits here are fixed. Floors and rational
intermediates define constants only and are not operations of the
Diophantine equation. The exact integer payloads and hashes are supplied.

\providecommand{\fl}[1]{\left\lfloor#1\right\rfloor}
\providecommand{\rg}[2]{\{#1,\ldots,#2\}}
'''
    return preamble + body

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, text in [('integer_residuals.tex', contents()), ('compact_constants.tex', constants())]:
        path = ROOT / name
        if args.check:
            if not path.is_file() or path.read_text() != text:
                raise ValueError('Literal manuscript mismatch: ' + name)
        else:
            path.write_text(text)
    print('PASS: 196 literal residuals and complete compact constant recipe')

if __name__ == '__main__':
    main()
