#!/usr/bin/env python3
"""Emit one finite polynomial DAG; Python standard library only."""
from pathlib import Path
import json
from collections import Counter

ROOT = Path(__file__).resolve().parent

def build():
    parent = json.loads((ROOT / 'inherited/equation_XY_bV.json').read_text())
    rows = []
    def r(name, op, left, right):
        rows.append([name, op, left, right])
    # Unchanged outer arithmetic from the authenticated 76-operation parent.
    for row in parent['source'][:34]:
        rows.append(row)
    # Replace Pell doubling by staged recovery of the main radicand.
    r('Delta', '*', 'Am1', 'Ap1')
    r('Delta_c2', '*', 'Delta', 'c2')
    r('Dm', '+', 'Delta_c2', 1)
    r('A', '+', 'Am1', 1)
    r('ic2', '*', 'i', 'c2')
    r('U', '*', 'A', 'ic2')
    r('S', '*', 'Dtau', 'Dm')
    r('US', '*', 'U', 'S')
    r('Delta_US', '*', 'Delta', 'US')
    r('a', '*', 'Delta_US', 'U')
    r('F2', '+', 'a', 1)
    r('Q', '*', 'Delta', 'a')
    r('Gstar', '*', 'S', 'F2')
    # Same unshifted auxiliary coordinate and same rational carrier.
    for row in parent['source'][44:]:
        name, op, left, right = row
        if name == 'Dg':
            continue
        left = {'Fsqr':'F2', 'Dg':'Gstar'}.get(left, left)
        right = {'Fsqr':'F2', 'Dg':'Gstar'}.get(right, right)
        r(name, op, left, right)
    counts = dict(sorted(Counter(row[1] for row in rows).items()))
    return {
        'name':'staged_main_square_XY_bV',
        'domain':parent['domain'],
        'witnesses':parent['witnesses'],
        'fixed_numerals':parent['fixed_numerals'],
        'coefficient_binding':parent['coefficient_binding'],
        'source':rows,
        'output':'N',
        'operations':len(rows),
        'operation_breakdown':counts,
        'exact_degree':454,
        'transport_weight':'bV',
        'denominator':'XY',
        'proof':'PROOF.md',
        'parent':'inherited/equation_XY_bV.json',
        'status':'Ordinary proof with inherited native/refutation calibration; no new formal-kernel endpoint.',
    }

if __name__ == '__main__':
    payload = build()
    output = ROOT / 'equation78_degree454.json'
    text = json.dumps(payload, indent=2) + '\n'
    if '--check' in __import__('sys').argv:
        if output.read_text() != text:
            raise SystemExit('Circuit regeneration differs')
        print('Circuit regeneration agrees')
    else:
        output.write_text(text)
        print(json.dumps({k:payload[k] for k in ['operations','operation_breakdown','exact_degree']}))
