#!/usr/bin/env python3
"""Read back the printed TeX residuals and authenticate the public equation.

This does not import the exporter or any producer. It parses the deliberately
small mathematical grammar of the literal appendix and compares sparse
integer coefficients, row order, dimensions, and public/stage copies.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def need(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    eqpath = ROOT / 'equation/equation.json'
    eq = json.loads(eqpath.read_text())
    for name in ['equation.json', 'expanded_polynomial.json', 'METRICS.json', 'beta_certificate.json']:
        need((ROOT / 'equation' / name).read_bytes() ==
             (ROOT / 'stages/principal225' / name).read_bytes(), 'public copy: ' + name)
    need((ROOT / 'inputs/parent245.json').read_bytes() ==
         (ROOT / 'inherited/joint_norm245/equation/equation.json').read_bytes(), 'parent copy')
    tex = (ROOT / 'report/residuals.tex').read_text()
    blocks = re.findall(r'\\begin\{align\*\}(.*?)\\end\{align\*\}', tex, re.S)
    need(len(blocks) == len(eq['residuals']), 'printed row count')
    term_count = 0
    for j, (block, row) in enumerate(zip(blocks, eq['residuals'])):
        prefix = re.match(r'\s*R_\{(\d+)\}=\{\}&', block)
        need(prefix is not None and int(prefix.group(1)) == j, 'printed row index')
        body = block[prefix.end():].replace('\\\\', '').replace('&{}', '')
        body = re.sub(r'\s+', '', body)
        if not body.startswith(('+', '-')):
            body = '+' + body
        parsed = {}
        for sign, coeff, variables in re.findall(r'([+-])(\d*)((?:x_\{\d+\}(?:\^\{2\})?)*)', body):
            need(bool(coeff or variables), 'empty printed term')
            indices = []
            for index, exponent in re.findall(r'x_\{(\d+)\}(\^\{2\})?', variables):
                indices.extend([int(index)] * (2 if exponent else 1))
            monomial = tuple(sorted(indices))
            need(monomial not in parsed, 'duplicate printed monomial')
            parsed[monomial] = (-1 if sign == '-' else 1) * (int(coeff) if coeff else 1)
        consumed = ''.join(m.group(0) for m in re.finditer(
            r'[+-]\d*(?:x_\{\d+\}(?:\^\{2\})?)*', body))
        need(consumed == body, 'unparsed TeX in row ' + str(j))
        need(parsed == {tuple(m): c for c, m in row['terms']}, 'printed coefficient row ' + str(j))
        term_count += len(parsed)
    met = json.loads((ROOT / 'equation/METRICS.json').read_text())
    macros = dict(re.findall(r'\\newcommand\{\\(\w+)\}\{([^}]+)\}',
                            (ROOT / 'report/metrics.tex').read_text()))
    need(macros == {'NumVars': '225', 'LastVar': '224', 'NumRows': '162', 'LastRow': '161',
                    'NumTerms': '7,867', 'CoeffHeight': '128,446'}, 'printed metrics')
    names = (ROOT / 'equation/variables.tsv').read_text().splitlines()
    need(names == ['index\tname\tkind'] + ['%d\t%s\t%s' % (i, v['name'], v['kind'])
                                         for i, v in enumerate(eq['variables'])], 'variable list')
    return {'result': 'passed', 'equation_sha256': hashlib.sha256(eqpath.read_bytes()).hexdigest(),
            'printed_residuals': len(blocks), 'printed_terms': term_count,
            'metrics': met, 'public_stage_copies_identical': True,
            'pinned_parent_copy_identical': True,
            'scope': 'Exact parsing of the literal TeX appendix, metadata, and public artifact copies.'}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--receipt', type=Path)
    args = ap.parse_args()
    result = main()
    payload = json.dumps(result, indent=2) + '\n'
    if args.receipt:
        args.receipt.write_text(payload)
    print(payload, end='')
