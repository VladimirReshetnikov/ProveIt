#!/usr/bin/env python3
"""Held exact literal row transformation; no optimizer or project imports."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = 'research/ten-positive-doubled-product-square'
SOURCE_SEAL = 'e9acadc97bd47672184229d9ea59a8f0b5857a3dfd5289f42af17d1af64e967f'
PROPOSAL = 'research/ten-positive-qcube-doubled'
PROPOSAL_SEAL = '8051545cea9a38d96c96d3542773aa10fa30c34f3993623d8bb40c02cfa9ab73'


def need(ok, why):
    if not ok:
        raise ValueError(why)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def authenticate():
    pins = json.loads((HERE / 'SOURCE_PINS.json').read_bytes())
    for group, folder in [('core', HERE), ('external_whole_files', ROOT)]:
        for name, record in pins[group].items():
            data = (folder / name).read_bytes()
            need(digest(data) == record['sha256'] and len(data) == record['bytes'],
                 'Whole reviewed input ' + name)
    copied = json.loads((HERE / 'COPIED_INPUTS.json').read_bytes())['files']
    for name, record in copied.items():
        data = (HERE / name).read_bytes()
        need(data == (ROOT / record['source']).read_bytes() and
             digest(data) == record['sha256'] and len(data) == record['bytes'],
             'Entire accepted local copy ' + name)


def construct():
    authenticate()
    artifacts, maps, metrics = {}, {}, []
    for old_number, new_number, degree in [(84, 81, 750), (85, 82, 560)]:
        parent_bytes = (HERE / f'parents/equation_{old_number}.json').read_bytes()
        parent = json.loads(parent_bytes)
        originals = {r[0]: list(r) for r in parent['source']}
        need(len(originals) == len(parent['source']), 'Unique accepted parent gates')
        deleted = {'P1', 'qm1Y', 'q3Bt', 'inner'}
        rewritten = {'P1mu2': ['P1mu2', '*', 'bJ', 'mu2'],
                     'mu2inner': ['mu2inner', '*', 'mu2', 'Bt'],
                     'P1e': ['P1e', '*', 'bJ', 'e'],
                     'brk': ['brk', '+', 'mu2inner', 'P1e'],
                     'Znum': ['Znum', '-', 'Zpart1', 'Zpart2']}
        rows = []
        for original in parent['source']:
            name = original[0]
            if name in deleted or name in {'q2', 'q3'}:
                continue
            rows.append(rewritten.get(name, list(original)))
            if name == 'q':
                rows.extend([originals['q2'], originals['q3'], ['Y', '*', 'q3', 's']])
        positions = {r[0]: index for index, r in enumerate(rows)}
        mapping = []
        for index, original in enumerate(parent['source']):
            name = original[0]
            action = ('deleted' if name in deleted else 'moved' if name in {'q2', 'q3'}
                      else 'rewritten' if name in rewritten else 'retained')
            mapping.append({'old_index': index, 'old_row': original, 'action': action,
                            'new_index': positions.get(name),
                            'new_row': None if name in deleted else rows[positions[name]]})
        maps[str(new_number)] = {'parent': old_number, 'rows': mapping,
                                'added': [{'new_index': positions['Y'], 'row': rows[positions['Y']]}],
                                'formal_old_input_substitution': {'Y': 'q^3*s', 'n': 'n-s'},
                                'scope': 'Formal polynomial row correspondence; not a positive old-tuple bijection.'}
        breakdown = dict(Counter(r[1] for r in rows))
        packet = {'name': 'qcube_doubled_product_square_' + parent['transport_weight'],
                  'domain': parent['domain'],
                  'witnesses': ['s' if name == 'Y' else name for name in parent['witnesses']],
                  'fixed_numerals': parent['fixed_numerals'],
                  'coefficient_binding': parent['coefficient_binding'], 'source': rows,
                  'output': 'N', 'operations': len(rows), 'operation_breakdown': breakdown,
                  'exact_degree': degree, 'transport_weight': parent['transport_weight'],
                  'proof': 'PROOF.md',
                  'proof_status': 'Complete ordinary positive maps relative to the whole accepted indexed/native contracts; canonical q^3|Y and R>3q retained. No page or Lean promotion.',
                  'parent': {'path': SOURCE + f'/equation_{old_number}.json',
                             'sha256': digest(parent_bytes), 'manifest_sha256': SOURCE_SEAL},
                  'ordinary_proposal': {'path': PROPOSAL + '/PROPOSAL.md',
                                        'manifest_sha256': PROPOSAL_SEAL}}
        name = f'data/equation_{new_number}.json'
        artifacts[name] = encoded(packet)
        metrics.append({'file': name, 'positive_inputs': len(packet['witnesses']),
                        'operations': len(rows), 'operation_breakdown': breakdown,
                        'claimed_degree_pending_independent_check': degree,
                        'scope': 'Counts of complete emitted rows, not manual parent-count subtraction.'})
    artifacts['data/ROW_MAPS.json'] = encoded(maps)
    artifacts['data/METRICS.json'] = encoded(metrics)
    artifacts['data/INDEX.json'] = encoded({
        'schema': 'qcube_doubled_full_literal_data_v1',
        'producer_sha256': digest(Path(__file__).read_bytes()),
        'scope': 'Complete two graphs and all row maps; no optimizer, hidden variable, or source rebuild.',
        'files': {name: {'sha256': digest(raw), 'bytes': len(raw)}
                  for name, raw in sorted(artifacts.items())}})
    return artifacts, metrics


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    artifacts, metrics = construct()
    for name, raw in artifacts.items():
        path = HERE / name
        if args.check or path.exists():
            need(path.is_file() and path.read_bytes() == raw, 'Exact deterministic artifact ' + name)
    if not args.check:
        for name, raw in artifacts.items():
            path = HERE / name
            if not path.exists():
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    report = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
              'mode': 'pure byte-exact rebuild' if args.check else 'literal graph materialization',
              'artifacts': {name: {'sha256': digest(raw), 'bytes': len(raw)}
                            for name, raw in sorted(artifacts.items())},
              'metrics': metrics, 'no_optimizer_or_parent_program': True}
    raw = encoded(report)
    args.output.write_bytes(raw)
    print(raw.decode(), end='')


if __name__ == '__main__':
    main()
