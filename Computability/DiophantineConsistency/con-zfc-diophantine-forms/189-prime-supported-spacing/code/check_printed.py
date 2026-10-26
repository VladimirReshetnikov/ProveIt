#!/usr/bin/env python3
"""Independently parse every printed residual and compare exact coefficients."""
import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def parse(tex):
    blocks = re.findall(r'\\begin\{align\*\}(.*?)\\end\{align\*\}', tex, flags=re.S)
    rows = []
    for i, block in enumerate(blocks):
        head = re.match(r'\s*R_\{(\d+)\}\s*=\{\}&', block)
        if not head or int(head.group(1)) != i:
            raise ValueError('Missing or out-of-order row heading')
        s = block[head.end():].replace('\\\\', '').replace('&{}', '')
        s = re.sub(r'\s+', '', s)
        if not s or s[0] not in '+-':
            s = '+' + s
        answer = {}
        for token in re.findall(r'[+-][^+-]+', s):
            sign = -1 if token[0] == '-' else 1
            body = token[1:]
            match = re.match(r'\d+', body)
            coefficient = int(match.group()) if match else 1
            tail = body[match.end():] if match else body
            indices = []
            while tail:
                m = re.match(r'x_\{(\d+)\}(?:\^\{(\d+)\})?', tail)
                if not m:
                    raise ValueError('Unparsed expression: ' + tail)
                indices += [int(m.group(1))] * (int(m.group(2)) if m.group(2) else 1)
                tail = tail[m.end():]
            key = tuple(sorted(indices))
            answer[key] = answer.get(key, 0) + sign * coefficient
        rows.append({m:c for m,c in answer.items() if c})
    return rows


def check():
    e = json.loads((ROOT / 'equations/equation.json').read_text())
    tex = (ROOT / 'report/residuals.tex').read_text()
    rows = parse(tex)
    expected = [{tuple(m):c for c,m in row['terms']} for row in e['residuals']]
    if rows != expected:
        raise ValueError('Printed equation differs from the JSON polynomial')
    # A print-corruption control must not be accepted.
    changed = tex.replace('x_{0}', '2x_{0}', 1)
    if parse(changed) == expected:
        raise ValueError('Print corruption was not detected')
    return {'status':'PASS', 'printed_residuals':len(rows),
            'printed_coefficients':sum(len(r) for r in rows),
            'deliberate_print_mutation_rejected':True}


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--receipt', type=Path)
    args = p.parse_args()
    result = json.dumps(check(), indent=2) + '\n'
    if args.receipt:
        args.receipt.write_text(result)
    print(result, end='')
