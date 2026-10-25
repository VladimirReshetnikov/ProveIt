#!/usr/bin/env python3
"""Print the complete literal residuals of the fixed 245-variable equation.

Adapted from the retained common-remainder appendix generator, with separate
displays per residual, exact plaintext output, and a source identity receipt.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / 'direct/equation/equation.json'


def term(coefficient, monomial, first=False, tex=True):
    sign = ('-' if coefficient < 0 else '') if first else (' - ' if coefficient < 0 else ' + ')
    size = abs(coefficient)
    scalar = str(size) if size != 1 or not monomial else ''
    counts = Counter(monomial)
    if tex:
        factors = ''.join('X_{%d}' % i + ('^{%d}' % e if e > 1 else '') for i, e in sorted(counts.items()))
    else:
        factors = '*'.join('X%d' % i + ('^%d' % e if e > 1 else '') for i, e in sorted(counts.items()))
        if scalar and factors:
            scalar += '*'
    return sign + scalar + factors


def generate():
    data = json.loads(SOURCE.read_text())
    if len(data['variables']) != 245 or len(data['residuals']) != 181:
        raise ValueError('Wrong literal equation dimensions')
    lines = [r'\begingroup', r'\small', r'\setlength{\jot}{2pt}',
             r'\setlength{\abovedisplayskip}{5pt}', r'\setlength{\belowdisplayskip}{5pt}']
    plain = ['P245(X0,...,X244) = sum(R_i^2 for i=0,...,180).', 'All 245 coordinates range over the integers.', '']
    for i, row in enumerate(data['residuals']):
        chunks = []
        current = ''
        weight = 0
        for j, (c, mon) in enumerate(row['terms']):
            piece = term(c, mon, j == 0)
            cost = 3 + len(str(abs(c))) + 6 * len(set(mon))
            if current and weight + cost > 72:
                chunks.append(current)
                current = ''
                weight = 0
            current += piece
            weight += cost
        if current:
            chunks.append(current)
        lines.append(r'\[\begin{aligned}')
        for j, chunk in enumerate(chunks):
            prefix = 'R_{%d} &={}' % i if j == 0 else r'&\quad{}'
            lines.append(prefix + chunk + (r'\\' if j + 1 < len(chunks) else ''))
        lines.append(r'\end{aligned}\]')
        plain.append('R%d = ' % i + ''.join(term(c, m, j == 0, False) for j, (c, m) in enumerate(row['terms'])))
    lines.extend([r'\endgroup', ''])
    tex = '\n'.join(lines)
    text = '\n'.join(plain) + '\n'
    return data, tex, text


def main():
    data, tex, text = generate()
    (ROOT / 'report/residuals.tex').write_text(tex)
    (ROOT / 'direct/equation/residuals.txt').write_text(text)
    variables = 'index\tconstruction_label\n' + ''.join('%d\t%s\n' % (i, v['name']) for i, v in enumerate(data['variables']))
    (ROOT / 'direct/equation/variables.tsv').write_text(variables)
    receipt = {'equation_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
               'variables': 245, 'residuals': 181,
               'residuals_tex_sha256': hashlib.sha256(tex.encode()).hexdigest(),
               'residuals_text_sha256': hashlib.sha256(text.encode()).hexdigest()}
    (ROOT / 'verification').mkdir(exist_ok=True)
    (ROOT / 'verification/appendix_generation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
