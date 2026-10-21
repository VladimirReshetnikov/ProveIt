#!/usr/bin/env python3
"""Replay the four exact finite implicational obstructions; no search."""
from itertools import product
from pathlib import Path
import argparse, hashlib, json, sys

if not __debug__ or sys.flags.optimize:
    raise SystemExit('Run without -O or PYTHONOPTIMIZE.')

def require(ok, message):
    if not ok:
        raise ValueError(message)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', nargs='?', type=Path,
                    default=Path(__file__).with_name('countermodels.json'))
    ap.add_argument('--output', type=Path)
    a = ap.parse_args()
    records = json.loads(a.certificate.read_text())
    require([x['restriction'] for x in records] == ['U=A', 'U=B', 'U=C', 'U=0'],
            'Exact four-case inventory')
    checked = []
    for r in records:
        n = r['size']; table = r['implication_table']
        require(n == 3 and r['truth'] == 0 and r['designated'] == [0], 'Matrix convention')
        require(len(table) == n and all(len(row) == n for row in table), 'Square table')
        require(all(type(v) is int and 0 <= v < n for row in table for v in row), 'Closed algebra')
        imp = lambda x, y: table[x][y]
        require(imp(0, 0) == 0, 'Collapsed truth alias')
        require(all(x != 0 or imp(x, y) != 0 or y == 0
                    for x, y in product(range(n), repeat=2)), 'Modus ponens preservation')
        for x, y, z in product(range(n), repeat=3):
            u = {'U=A': x, 'U=B': y, 'U=C': z, 'U=0': 0}[r['restriction']]
            require(imp(imp(imp(z, u), x), imp(imp(x, z), imp(y, z))) == 0,
                    'A restricted axiom is not designated')
        require(r['counterexamples'], 'Missing failing classical formula')
        for c in r['counterexamples']:
            x, y = c['p'], c['q']
            require(c['theorem'] in ('K', 'Peirce'), 'Unknown classical formula')
            value = imp(x, imp(y, x)) if c['theorem'] == 'K' else imp(imp(imp(x, y), x), x)
            require(value == c['value'] and value != 0, 'Invalid counterexample')
        checked.append({'restriction': r['restriction'], 'axiom_assignments': 27,
                        'classical_counterexamples': len(r['counterexamples'])})
    result = {'status': 'FOUR_EXACT_IMPLICATIONAL_COUNTERMODELS_PASS',
              'certificate_sha256': hashlib.sha256(a.certificate.read_bytes()).hexdigest(),
              'checked': checked,
              'scope': 'Truth, modus ponens and one restricted rho8 schema only. Quantifier, equality and set-theoretic rows are not modeled.'}
    data = json.dumps(result, indent=2) + '\n'
    if a.output:
        a.output.write_text(data)
    print(data, end='')

if __name__ == '__main__':
    main()
