#!/usr/bin/env python3
"""Typeset every principal residual, with an exact parser round trip."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def term_tex(c, mon, first=False):
    sign = '-' if c < 0 else ('' if first else '+')
    factors = []
    for i, power in sorted(Counter(mon).items()):
        factors.append('z_{' + str(i) + '}' + ('^{' + str(power) + '}' if power > 1 else ''))
    body = ''.join(factors)
    coefficient = str(abs(c)) if abs(c) != 1 or not body else ''
    return sign + coefficient + body


def parse_term(s):
    m = re.fullmatch(r'([+-]?)(\d*)((?:z_\{\d+\}(?:\^\{\d+\})?)*)', s)
    if not m:
        raise ValueError('Invalid printed term: ' + repr(s))
    sign, magnitude, factors = m.groups()
    if not magnitude and not factors:
        raise ValueError('Empty printed term')
    c = int(magnitude or '1') * (-1 if sign == '-' else 1)
    mon = []
    for i, power in re.findall(r'z_\{(\d+)\}(?:\^\{(\d+)\})?', factors):
        mon.extend([int(i)] * int(power or '1'))
    return [c, mon]


def build(source):
    raw = source.read_bytes()
    equation = json.loads(raw)
    lines = [r'\begingroup\small', r'\setlength{\jot}{2pt}', r'\allowdisplaybreaks[4]']
    recovered = []
    for i, row in enumerate(equation['residuals']):
        terms = row['terms']
        printed = [term_tex(c, mon, j == 0) for j, (c, mon) in enumerate(terms)]
        parsed = [parse_term(t) for t in printed]
        if parsed != terms:
            raise ValueError('Literal TeX round trip failed at residual ' + str(i))
        recovered.append(parsed)
        chunks, chunk, width = [], [], 0
        for term, (c, mon) in zip(printed, terms):
            estimate = 9 + 4 * len(str(abs(c))) + sum(8 + 3 * len(str(v)) for v in mon)
            if chunk and width + estimate > 365:
                chunks.append(chunk)
                chunk, width = [], 0
            chunk.append(term)
            width += estimate
        if chunk:
            chunks.append(chunk)
        lines.append(r'\begin{align*}')
        for j, chunk in enumerate(chunks):
            prefix = 'r_{' + str(i) + '} &=' if j == 0 else r'&\quad '
            lines.append(prefix + ''.join(chunk) + (r'\\' if j + 1 < len(chunks) else ''))
        lines.append(r'\end{align*}')
    lines.append(r'\endgroup')
    body = '\n'.join(lines) + '\n'
    # Parse the emitted full document, not just the pre-layout token list.
    blocks = re.findall(r'\\begin\{align\*\}(.*?)\\end\{align\*\}', body, re.S)
    back = []
    for i, block in enumerate(blocks):
        block = re.sub(r'^\s*r_\{\d+\}\s*&=', '', block)
        block = block.replace('\\\\', '').replace('&\\quad ', '').replace('\n', '').strip()
        toks = re.findall(r'[+-]?[^+-]+', block)
        back.append([parse_term(t) for t in toks])
    if back != recovered:
        raise ValueError('Final emitted appendix does not reconstruct every original residual')
    receipt = {'status': 'PASS', 'source': source.relative_to(ROOT).as_posix(),
               'source_sha256': hashlib.sha256(raw).hexdigest(),
               'residuals': len(recovered), 'row_terms': sum(map(len, recovered)),
               'variables': len(equation['variables']),
               'tex_sha256': hashlib.sha256(body.encode()).hexdigest(),
               'scope': 'exact equality of the printed residuals and literal JSON'}
    return body, receipt


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--source', type=Path, default=ROOT/'direct/equations/principal239/natural/equation.json')
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    body, receipt = build(args.source)
    output = HERE/'residuals.tex'
    if args.check:
        if output.read_text() != body:
            raise ValueError('Printed residuals differ from exact reconstruction')
    else:
        output.write_text(body)
        (ROOT/'review/PRINTED_RESIDUALS.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, sort_keys=True))


if __name__ == '__main__':
    main()
