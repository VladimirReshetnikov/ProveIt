#!/usr/bin/env python3
"""Recollect the literal quartic and export its complete TeX residual list.

The collector uses only the Python standard library and imports no producer.
It verifies the supplied expanded coefficients before writing report inputs.
"""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json
import math

ROOT = Path(__file__).resolve().parents[1]

def require(ok, message):
    if not ok:
        raise ValueError(message)

def inspect(directory):
    equation = json.loads((directory / 'equation.json').read_text())
    expanded = json.loads((directory / 'expanded_polynomial.json').read_text())
    count = len(equation['variables'])
    total = Counter()
    live = set()
    for row in equation['residuals']:
        terms = row['terms']
        for c, mon in terms:
            require(isinstance(c, int) and c != 0, 'Invalid residual coefficient')
            require(len(mon) <= 2, 'Nonquadratic residual')
            require(all(isinstance(i, int) and 0 <= i < count for i in mon), 'Bad index')
            live.update(mon)
        for c, mon in terms:
            for d, other in terms:
                total[tuple(sorted(mon + other))] += c * d
    actual = {m: c for m, c in total.items() if c}
    expected = {tuple(mon): c for c, mon in expanded['terms']}
    require(len(expected) == len(expanded['terms']), 'Duplicate expanded term')
    require(actual == expected, 'Expanded polynomial differs from residual squares')
    require(live == set(range(count)), 'Unused variable in literal equation')
    metrics = {
        'variables': count,
        'rows': len(equation['residuals']),
        'degree': max(map(len, actual)),
        'monomials': len(actual),
        'height': max(map(abs, actual.values())),
        'residual_terms': sum(len(r['terms']) for r in equation['residuals']),
    }
    measured = json.loads((directory / 'METRICS.json').read_text())
    for key in ['variables', 'rows', 'degree', 'monomials', 'height']:
        require(metrics[key] == measured[key], 'Wrong metric: ' + key)
    require(metrics['degree'] == 4, 'Not an attained quartic')
    return equation, metrics

def monomial(c, indices, first=False):
    sign = '-' if c < 0 else ('' if first else '+')
    c = abs(c)
    powers = Counter(indices)
    factors = ''.join('z_{%d}' % i + ('^{%d}' % e if e > 1 else '')
                      for i, e in sorted(powers.items()))
    coefficient = str(c) if c != 1 or not factors else ''
    term = sign + coefficient + factors
    width = 0.9 + 0.6 * len(coefficient)
    width += sum(1.05 + 0.46 * len(str(i)) + (0.5 if e > 1 else 0)
                 for i, e in powers.items())
    return term, width

def latex_rows(equation):
    out = ['% Generated from the literal quadratic residuals; do not edit by hand.',
           r'\begingroup\small', r'\allowdisplaybreaks[4]']
    for j, row in enumerate(equation['residuals']):
        lines, line, width = [], [], 0.0
        for n, (c, mon) in enumerate(row['terms']):
            s, w = monomial(c, mon, n == 0)
            if line and width + w > 39:
                lines.append(' '.join(line))
                line, width = [], 0.0
            line.append(s)
            width += w
        if line:
            lines.append(' '.join(line))
        out.append(r'\begin{align*}')
        for k, line in enumerate(lines):
            prefix = ('R_{%d}={}&' % j) if k == 0 else '&'
            ending = r'\\*' if k + 1 < len(lines) else ''
            out.append(prefix + line + ending)
        out.append(r'\end{align*}')
    out.append(r'\endgroup')
    return '\n'.join(out) + '\n'

def products():
    eq, main = inspect(ROOT / 'direct/equations/P242')
    _, balanced = inspect(ROOT / 'direct/equations/P243')
    macros = ['% Exact independently recollected metrics.']
    fields = [('Variables', 'variables'), ('Rows', 'rows'), ('Terms', 'monomials'), ('Height', 'height')]
    for prefix, m in [('Main', main), ('Balanced', balanced)]:
        for label, key in fields:
            macros.append(r'\newcommand{\%s%s}{%s}' % (prefix, label, format(m[key], ',')))
    macros += [r'\newcommand{\LastRow}{%d}' % (main['rows'] - 1),
               r'\newcommand{\LastVariable}{%d}' % (main['variables'] - 1)]
    return {'metrics.tex': '\n'.join(macros) + '\n', 'residuals.tex': latex_rows(eq)}, {
        'status': 'pass', 'main': main, 'balanced': balanced,
        'scope': 'Independent full coefficient recollection and exact TeX export; no semantic proof claim.'}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    files, receipt = products()
    hashes = {}
    for name, value in files.items():
        path = ROOT / 'report' / name
        if args.check:
            require(path.read_text() == value, 'Generated report input differs: ' + name)
        else:
            path.write_text(value)
        hashes[name] = hashlib.sha256(value.encode()).hexdigest()
    receipt['generated_sha256'] = hashes
    text = json.dumps(receipt, indent=2) + '\n'
    if args.receipt:
        args.receipt.write_text(text)
    print(text, end='')

if __name__ == '__main__':
    main()
