#!/usr/bin/env python3
"""Rebuild the eight inherited/comparison circuits from preserved sources.

Usage: python3 code/refactor_comparison_circuits.py
Only the bundled, SHA-256-pinned upstream JSON packets are read. No checkout,
network access or third-party package is required. Afterwards run
code/bind_coefficients.py to apply the current complete coefficient tuple.
"""
import json
from pathlib import Path
from circuit_tools import audit_dag, digest, require, source_digest

ROOT = Path(__file__).resolve().parents[1]
DIRECT = {'baseline67': 'baseline67_source.json',
          'retained59_system': 'retained59_source.json'}
KINDS = ['norm12_product', 'norm12_system', 'merger12_product',
         'merger12_system', 'merger13_product', 'merger13_system']


def refactor_norm(p):
    """Factor V1 out of every odd coefficient, retaining G*V1^2."""
    rows = []
    is_system = 'comparisons' in p
    dropped = {'SL', 'V1', 'C1', 'Kc1', 'Csyy'}
    if is_system:
        dropped.add('N')
    replacement = {
        'CsGyy': ['CsGyy', '*', 'theta2', 'd2'],
        'Csxy': ['Csxy', '*', 'C0', 'd'],
        'W1': ['W1', '-', 'Cs1', 'Kf'],
        'WsGyy': ['WsGyy', '*', 'theta2', 'Wsyy'],
        'fourKZ1': ['fourKZ1', '*', 'fourZ', 'Kf'],
        'GN11': ['GN11', '*', 'theta2', 'N11']}
    names = {row[0] for row in p['source']}
    require(dropped | set(replacement) <= names, 'unexpected norm source schema')
    for row in p['source']:
        n = row[0]
        if n in dropped:
            continue
        rows.append(replacement.get(n, row))
        if n == 'V0':
            rows += [['theta2pre', '*', 'S2', 'L2G'],
                     ['theta2', '*', 4, 'theta2pre']]
    q = dict(p, source=rows)
    if is_system:
        require(p['comparisons'] == [['Nk', 1], ['Nt', 1], ['N', 0]],
                'unexpected norm system comparisons')
        q['comparisons'] = [['Nk', 1], ['Nt', 1], ['N00', 'GN11']]
    return q


def refactor_monic(p):
    """Share B*(2W)^2 and remove a common factor from the odd part."""
    twelve = len(p['witnesses']) == 12
    require(twelve or len(p['witnesses']) == 13, 'unexpected merger dimension')
    dropped = {'r1', 'r1sq', 'himag'}
    if twelve:
        dropped.update({'vimag', 'urealr1'})
    rows = []
    for row in p['source']:
        n = row[0]
        if n in dropped:
            continue
        if n == 'Br1sq':
            rows += [['BW2', '*', 'B', 'W2'], ['Br1sq', '*', 4, 'BW2']]
        elif twelve and n == 'vimag2':
            rows.append(['vimagcore2', '*', 'vimagcore', 'vimagcore'])
        elif twelve and n == 'Bvimag2':
            rows.append(['Bvimag2', '*', 'Br1sq', 'vimagcore2'])
        elif twelve and n == 'vrealvimag':
            rows.append(['vrealvimag', '*', 'vreal', 'vimagcore'])
        elif twelve and n == 'coefur':
            rows.append(['coefur', '*', 'coef', 'ureal'])
        elif n == 'norm_imag_square':
            a = 'himaghalf' if twelve else 'imagCore'
            rows.append([n, '*', a, a])
        elif n == 'B_norm_imag_square':
            if twelve:
                rows += [['four_norm_imag_square', '*', 4, 'norm_imag_square'],
                         [n, '*', 'Br1sq', 'four_norm_imag_square']]
            else:
                rows.append([n, '*', 'Br1sq', 'norm_imag_square'])
        else:
            rows.append(row)
    require(dropped <= {r[0] for r in p['source']}, 'unexpected merger source schema')
    return dict(p, source=rows)


def main():
    pins = json.loads((ROOT/'evidence/SOURCE_PINS.json').read_text())
    hashes = {r['local_path']: r['sha256'] for r in pins['files']}
    mappings = dict(DIRECT)
    mappings.update({'optimized_' + n: n + '_source.json' for n in KINDS})
    rows = []
    for name, original in mappings.items():
        local = 'upstream/' + original
        raw = (ROOT/local).read_bytes()
        require(digest(raw) == hashes[local], 'preserved source digest mismatch: ' + local)
        p = json.loads(raw)
        if name.startswith('optimized_norm'):
            p = refactor_norm(p)
        elif name.startswith('optimized_merger'):
            p = refactor_monic(p)
        p['name'] = name
        p['ledger'] = audit_dag(p, check_ledger=False)
        path = ROOT/'circuits'/(name + '.json')
        path.write_text(json.dumps(p, indent=2) + '\n')
        rows.append(dict(file=str(path.relative_to(ROOT)),
                         operations=p['ledger']['operations'],
                         source_sha256=source_digest(p['source']),
                         preserved_source=local, preserved_sha256=digest(raw)))
    receipt = dict(status='PASS', packets=rows,
                   scope='Deterministic arithmetic refactoring of preserved symbolic-port circuits. Coefficients are bound separately.')
    (ROOT/'evidence/COMPARISON_REBUILD.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', rebuilt_circuits=len(rows)), indent=2))


if __name__ == '__main__':
    main()
