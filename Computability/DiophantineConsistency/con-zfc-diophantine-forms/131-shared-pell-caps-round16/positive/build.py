"""Build the doubly saturated single-square graphs; execute no source code."""
import argparse
import collections
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def build(direct=False, lean=False):
    parent = ROOT / 'parents' / ('direct_uncentered.json' if direct else 'uncentered.json')
    data = json.loads(parent.read_text())
    rows = []
    removed = {'nV', 'dM2', 'Dg', 'fg', 'fy', 'root_sum', 'root_gap', 'gap2', 'fgfy', 'fourfgfy', 'N'}
    for row in data['source']:
        name, op, a, b = row
        if name in removed:
            continue
        if name == 'U':
            # Delta is independent of the strong ordinate; move it before U.
            rows.extend([
                ['Delta', '*', 'Am1', 'Ap1'],
                ['Afull', '+', 'Am1', 1],
                ['Kc0', '*', 'Delta', 'c2'],
                ['Kc', '+', 'Kc0', 1],
                ['Ubase', '*', 'i', 'c2'],
                ['UA', '*', 'Ubase', 'Afull'],
                ['U', '*', 'UA', 'Kc'],
            ])
            continue
        if name == 'Delta':
            continue
        if name == 'Dnum':
            rows.append(row)
            rows.extend([['Dg', '*', 'Dtau', 'Df'], ['Radnum', '*', 'Dg', 'Dnum']])
            if lean:
                rows.append(['Lmajor', '*', 'SE', 'DfcTR'])
            continue
        if name == 'LBt':
            row = [name, op, 'Lmajor' if lean else 'V2', b]
        if name == 'center':
            row = [name, op, 'n', b]
        rows.append(row)
    rows.extend([['rhs', '*', 'M2', 'Radnum'], ['N', '-', 'fs', 'rhs']])
    name = ('direct_' if direct else '') + ('single_square_lean' if lean else 'single_square')
    degree = (334 if direct else 380) if lean else (384 if direct else 436)
    data.update(name=name, source=rows, operations=len(rows),
                operation_breakdown=dict(collections.Counter(r[1] for r in rows)),
                exact_degree=degree, proof='PROOF.md',
                parent_sha256=hashlib.sha256(parent.read_bytes()).hexdigest(),
                mechanism='A(1+Delta*c^2) saturation and one square; all fixed ports retained jointly')
    return data

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    results = []
    for direct in [False, True]:
        for lean in [False, True]:
            data = build(direct, lean)
            target = ROOT / 'equations' / (data['name'] + '.json')
            text = json.dumps(data, indent=2) + '\n'
            if args.check:
                if target.read_text() != text:
                    raise RuntimeError('Graph differs: ' + str(target))
            else:
                target.write_text(text)
            results.append({k: data[k] for k in ['name', 'operations', 'operation_breakdown', 'exact_degree']})
    print(json.dumps(results, indent=2))

if __name__ == '__main__':
    main()
