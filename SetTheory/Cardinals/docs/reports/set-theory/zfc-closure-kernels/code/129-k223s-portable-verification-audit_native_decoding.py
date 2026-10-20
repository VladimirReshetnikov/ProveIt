#!/usr/bin/env python3
"""Check uniform arithmetic side conditions for the generated named decoding.

This checks constructor-shape side conditions, not first-order consistency.
For implication the pinned decoder has exceptions at code0 and consequent1.
The assertion that R(c,a) and R(c,b) differ from1 uses the unchanged gate.
"""
from pathlib import Path
import argparse, hashlib, json


def is_node(f): return isinstance(f, (list, tuple))
def pair(a, b): return (a+b)*(a+b+1)//2+b


def lower(f):
    if not is_node(f): return f if isinstance(f, int) else 0
    op, a, b = f
    # Only positivity and distinction from1 are needed. Saturation keeps the
    # exact monotone lower-bound claim without constructing enormous codes.
    return min(2, 4*pair(lower(a), lower(b))+{'I': 0, 'R': 1, 'Q': 2, 'E': 3}[op])


def not_one(f):
    if not is_node(f): return isinstance(f, int) and f != 1
    op, a, b = f
    if op in ('I', 'Q', 'E'): return True
    if lower(a) > 0 or lower(b) > 0: return True
    return (a == 'c' and b in ('a', 'b')) or (b == 'c' and a in ('a', 'b'))


def check(expr):
    counts = dict(negations=0, implications=0, quantifiers=0,
                  memberships=0, equalities=0, opaque_matrix_occurrences=0)
    def visit(f):
        if not is_node(f):
            assert f == 'c', ('Unexpected standalone formula value', f)
            counts['opaque_matrix_occurrences'] += 1
            return
        op, a, b = f
        if op == 'I':
            if b == 1:
                counts['negations'] += 1
                visit(a)
            else:
                assert not_one(b), ('Consequent might decode as negation', b)
                assert lower(a) > 0 or lower(b) > 0, ('Implication might be code0', f)
                counts['implications'] += 1
                visit(a); visit(b)
        elif op == 'Q':
            counts['quantifiers'] += 1
            visit(b)
        else:
            assert op in ('R', 'E')
            counts['memberships' if op == 'R' else 'equalities'] += 1
    visit(expr)
    assert lower(expr) > 1, 'The bundle might accidentally be0 or1'
    return counts


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('variants', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    args=ap.parse_args()
    raw=args.variants.read_bytes(); data=json.loads(raw)
    if isinstance(data, dict): data=[data]
    results=[dict(name=v['name'], counts=check(v['expression'])) for v in data]
    report=dict(status='UNIFORM_NAMED_DECODER_SIDE_CONDITIONS_PASS',
                input_sha256=hashlib.sha256(raw).hexdigest(), variants=len(results),
                hypothesis='c!=a and c!=b', results=results,
                scope='Arithmetic constructor side conditions only. Reuses pinned D_wn, D_wal, D_wel, D_weq, and D_wim. Does not establish theory calibration, source execution, or machine runtime.')
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','variants','hypothesis')}))


if __name__=='__main__': main()
