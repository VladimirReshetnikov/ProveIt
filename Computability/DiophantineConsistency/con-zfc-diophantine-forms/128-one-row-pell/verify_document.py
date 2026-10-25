#!/usr/bin/env python3
"""Bind the human-readable equations and report metadata to the complete JSON.

This uses an intentionally narrow parser, not an equation-producer import.
It checks literal polynomials and file hashes, not their unbounded meaning.
"""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import argparse
import json
import re

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text())


def polynomial(terms):
    result = Counter()
    for coefficient, factors in terms:
        result[tuple(sorted(factors))] += coefficient
    return {m: c for m, c in result.items() if c}


def parse_polynomial(expression, tex=False):
    if tex:
        expression = expression.replace('\\\\', '').replace('&', '')
        expression = re.sub(r'\s+', '', expression).removesuffix('.')
        factor_pattern = re.compile(r'z_\{(\d+)\}(?:\^\{(\d+)\})?')
    else:
        expression = re.sub(r'[\s*]', '', expression)
        factor_pattern = re.compile(r'z(\d+)(?:\^(\d+))?')
    parts = re.findall(r'[+-]?[^+-]+', expression)
    require(''.join(parts) == expression and bool(parts), 'complete tokenization')
    terms = []
    for part in parts:
        sign = -1 if part.startswith('-') else 1
        body = part.lstrip('+-')
        coefficient = re.match(r'\d+', body)
        if coefficient:
            number = int(coefficient.group())
            body = body[coefficient.end():]
        else:
            number = 1
        factors = []
        while body:
            factor = factor_pattern.match(body)
            require(factor is not None, 'unexpected polynomial syntax: ' + body)
            factors.extend([int(factor.group(1))] * int(factor.group(2) or 1))
            body = body[factor.end():]
        terms.append((sign * number, factors))
    return polynomial(terms)


def run():
    claims = read_json(HERE / 'portable/CLAIMS.json')
    macros = dict(re.findall(r'\\newcommand\{\\(\w+)\}\{([^{}]*)\}',
                             (HERE / 'report/metrics.tex').read_text()))
    counts = {}
    for endpoint, prefix in [('integer378', 'Int'), ('natural242', 'Nat')]:
        claim = claims[endpoint]
        equation_path = HERE / 'portable' / claim['equation_path']
        expanded_path = HERE / 'portable' / claim['full_polynomial_path']
        equation = read_json(equation_path)
        expanded = read_json(expanded_path)
        for path, key, suffix in [
            (equation_path, 'equation_sha256', 'EquationHash'),
            (expanded_path, 'full_polynomial_sha256', 'PolynomialHash'),
        ]:
            digest = sha256(path.read_bytes()).hexdigest()
            require(digest == claim[key] == macros[prefix + suffix],
                    endpoint + ' report/claim/file hash')
        expected = {
            'Vars': len(equation['variables']),
            'Rows': len(equation['residuals']),
            'LastVar': len(equation['variables']) - 1,
            'LastRow': len(equation['residuals']) - 1,
            'Terms': len(expanded['terms']),
            'Height': max(abs(c) for c, m in expanded['terms']),
        }
        for suffix, value in expected.items():
            require(int(macros[prefix + suffix].replace(',', '')) == value,
                    endpoint + ' report metric ' + suffix)
        require(claim['variables'] == expected['Vars'], 'claim variables')
        require(claim['quadratic_residuals'] == expected['Rows'], 'claim rows')
        require(claim['monomials'] == expected['Terms'], 'claim monomials')
        require(claim['coefficient_height'] == expected['Height'], 'claim height')
        require(claim['exact_degree'] == max(len(m) for c, m in expanded['terms']),
                'claim exact degree')
        txt = (equation_path.parent / 'residuals.txt').read_text()
        text_rows = re.findall(r'^R(\d+) = (.+)$', txt, flags=re.MULTILINE)
        require(len(text_rows) == expected['Rows'], endpoint + ' complete text rows')
        for index, (row_id, expression) in enumerate(text_rows):
            require(int(row_id) == index, endpoint + ' text row order')
            require(parse_polynomial(expression) == polynomial(equation['residuals'][index]['terms']),
                    endpoint + ' text polynomial ' + row_id)
        counts[endpoint] = {'text_rows_checked': len(text_rows), 'metrics_and_hashes': 'PASS'}
        if endpoint == 'integer378':
            tex = (HERE / 'report/integer_residuals.tex').read_text()
            tex_rows = re.findall(
                r'\\begin\{align\*\}\s*r_\{(\d+)\}=\{\}&(.*?)\\end\{align\*\}',
                tex, flags=re.DOTALL)
            require(len(tex_rows) == expected['Rows'], 'complete TeX residual list')
            require(tex.count('\\begin{align*}') == len(tex_rows), 'no unmatched TeX rows')
            for index, (row_id, expression) in enumerate(tex_rows):
                require(int(row_id) == index, 'TeX row order')
                require(parse_polynomial(expression, tex=True) == polynomial(equation['residuals'][index]['terms']),
                        'TeX polynomial ' + row_id)
            counts[endpoint]['tex_rows_checked'] = len(tex_rows)
    return {'status': 'PASS', 'endpoints': counts,
            'scope': 'Every printed integer residual, both text equation lists, all report metrics and exact file hashes.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = json.dumps(run(), indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(output)
    print(output, end='')
