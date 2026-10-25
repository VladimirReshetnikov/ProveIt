#!/usr/bin/env python3
"""Render the complete natural equation and verify the TeX by parsing it back.

Run without arguments to write residuals.tex, residuals.txt and variables.tsv.
Run with --check to require byte-for-byte deterministic output without writing.
Both modes reconstruct every printed TeX polynomial and compare it with the
source equation.  This script uses only the Python standard library.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
TERMS_PER_LINE = 3


def term(coefficient, monomial, tex=True):
    sign = '+' if coefficient > 0 else '-'
    magnitude = abs(coefficient)
    factors = []
    if magnitude != 1 or not monomial:
        factors.append(str(magnitude))
    for index, exponent in sorted(Counter(monomial).items()):
        factor = 'x_{' + str(index) + '}' if tex else 'x' + str(index)
        if exponent > 1:
            factor += ('^{' + str(exponent) + '}') if tex else '^' + str(exponent)
        factors.append(factor)
    return sign + ('' if tex else '*').join(factors)


def generate(equation):
    tex = [
        '% Generated from natural/equation.json; all residuals are printed.',
        '% All x_i independently range over the nonnegative integers.',
        r'\begingroup',
        r'\small',
        r'\setlength{\tabcolsep}{2pt}',
        r'\setlength{\LTleft}{0pt}',
        r'\begin{longtable}{@{}r@{\;}l@{}}',
    ]
    plain = [
        '# All x_i independently range over the nonnegative integers.',
        '# P(x) = sum(s_j(x)^2 for j = 0,...,' + str(len(equation['residuals']) - 1) + ').',
    ]
    for index, row in enumerate(equation['residuals']):
        rendered = [term(c, m) for c, m in row['terms']]
        readable = [term(c, m, False) for c, m in row['terms']]
        if not rendered:
            raise ValueError('Empty residual ' + str(index))
        if rendered[0].startswith('+'):
            rendered[0] = rendered[0][1:]
        if readable[0].startswith('+'):
            readable[0] = readable[0][1:]
        plain.append('s_' + str(index) + ' = ' + ' '.join(readable))
        for offset in range(0, len(rendered), TERMS_PER_LINE):
            label = r'\(s_{' + str(index) + r'}=\)' if offset == 0 else ''
            last = offset + TERMS_PER_LINE >= len(rendered)
            tex.append(label + r' & \(\displaystyle '
                       + ' '.join(rendered[offset:offset + TERMS_PER_LINE])
                       + r'\) \\' + ('[3pt]' if last else ''))
    tex.extend([r'\end{longtable}', r'\endgroup', ''])
    variables = ['index\tsource_name\tsource_kind']
    variables.extend(
        str(index) + '\t' + variable['name'] + '\t' + variable.get('kind', '')
        for index, variable in enumerate(equation['variables'])
    )
    return {
        'residuals.tex': '\n'.join(tex),
        'residuals.txt': '\n'.join(plain) + '\n',
        'variables.tsv': '\n'.join(variables) + '\n',
    }


def parse_tex(equation):
    """Parse the generated TeX grammar, independently reconstructing each row."""
    groups = {}
    index = None
    for line in (ROOT / 'residuals.tex').read_text(encoding='utf-8').splitlines():
        if r'& \(\displaystyle ' not in line:
            continue
        label = re.search(r's_\{(\d+)\}=', line)
        if label:
            index = int(label.group(1))
            if index in groups:
                raise ValueError('Duplicate TeX residual ' + str(index))
            groups[index] = ''
        if index is None:
            raise ValueError('Unlabelled first residual')
        rhs = line.split(r'& \(\displaystyle ', 1)[1].split(r'\)', 1)[0]
        groups[index] += rhs
    if sorted(groups) != list(range(len(equation['residuals']))):
        raise ValueError('TeX residual index list differs from equation')
    for index, expression in groups.items():
        expression = expression.replace(' ', '')
        parsed = defaultdict(int)
        tokens = re.findall(r'[+-]?[^+-]+', expression)
        if ''.join(tokens) != expression:
            raise ValueError('Malformed TeX expression ' + str(index))
        for token in tokens:
            match = re.fullmatch(
                r'([+-]?)(\d*)((?:x_\{\d+\}(?:\^\{\d+\})?)*)', token)
            if not match:
                raise ValueError('Unparsed TeX token ' + token)
            sign, number, body = match.groups()
            coefficient = int(number or '1') * (-1 if sign == '-' else 1)
            indices = []
            for variable, exponent in re.findall(
                    r'x_\{(\d+)\}(?:\^\{(\d+)\})?', body):
                indices.extend([int(variable)] * int(exponent or '1'))
            parsed[tuple(sorted(indices))] += coefficient
        terms = [[c, list(m)] for m, c in sorted(parsed.items()) if c]
        if terms != equation['residuals'][index]['terms']:
            raise ValueError('TeX polynomial differs at residual ' + str(index))
    return len(groups)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true',
                        help='check deterministic output without writing files')
    arguments = parser.parse_args()
    equation = json.loads((ROOT / 'equation.json').read_text(encoding='utf-8'))
    outputs = generate(equation)
    for name, contents in outputs.items():
        path = ROOT / name
        if arguments.check:
            if path.read_text(encoding='utf-8') != contents:
                raise ValueError('Rendered text differs: ' + name)
        else:
            path.write_text(contents, encoding='utf-8')
    print(json.dumps({
        'status': 'PASS',
        'tex_rows_parsed': parse_tex(equation),
        'variables': len(equation['variables']),
        'files': list(outputs),
    }))


if __name__ == '__main__':
    main()
