#!/usr/bin/env python3
"""Parse the displayed TeX residuals independently and compare literal terms."""
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def main():
    text = (HERE / 'direct_residuals.tex').read_text()
    equation = json.loads((HERE.parent / 'direct/integer381/equation.json').read_text())
    rows = re.findall(r'R_\{(\d+)\}\s*&=\s*(.*?)(?=R_\{\d+\}\s*&=|\\end\{align\*\})', text, re.S)
    if len(rows) != len(equation['residuals']):
        raise ValueError('Wrong number of displayed residuals')
    count = 0
    for index, ((number, body), expected) in enumerate(zip(rows, equation['residuals'])):
        if int(number) != index:
            raise ValueError('Residual order differs')
        body = body.replace('\\quad', '').replace('\\\\', '').replace('&', '')
        body = re.sub(r'\s+', '', body)
        terms = []
        for part in re.findall(r'[+-]?[^+-]+', body):
            match = re.match(r'^([+-]?)(\d*)', part)
            coefficient = (-1 if match[1] == '-' else 1) * (int(match[2]) if match[2] else 1)
            rest = part[match.end():]
            monomial = []
            while rest:
                factor = re.match(r'z_\{(\d+)\}(?:\^\{(\d+)\})?', rest)
                if factor is None:
                    raise ValueError('Unexpected TeX in residual ' + number + ': ' + rest)
                monomial.extend([int(factor[1])] * int(factor[2] or 1))
                rest = rest[factor.end():]
            terms.append([coefficient, sorted(monomial)])
        order = lambda term: (term[1], term[0])
        if sorted(terms, key=order) != sorted(expected['terms'], key=order):
            raise ValueError('Displayed polynomial differs at residual ' + number)
        count += len(terms)
    print(json.dumps({'status': 'PASS', 'residuals': len(rows), 'literal_terms': count,
                      'method': 'independent TeX term parser; no equation generator imported'}, sort_keys=True))


if __name__ == '__main__':
    main()
