#!/usr/bin/env python3
"""CODE ONLY / HOLD: exact private-Tp deletion in four complete parent graphs."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CASES = [('unsheared_V2', 'doubled_84', 436), ('unsheared_bV', 'doubled_85', 328),
         ('qcube_V2', 'qcube_81', 750), ('qcube_bV', 'qcube_82', 560)]
SCOPE = ('Positive-zero equivalence uses the sealed ordinary V2 or general bV theorem; '
         'formal T_old=T-alpha is not a positive inverse. Whole indexed/native contracts retained.')


def need(ok, why):
    if not ok:
        raise ValueError(why)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def load(path):
    return json.loads(path.read_bytes())


def authenticate():
    pins = load(HERE / 'SOURCE_PINS.json')
    for group, folder in [('core', HERE), ('external_whole_files', ROOT)]:
        for name, record in pins[group].items():
            raw = (folder / name).read_bytes()
            need(digest(raw) == record['sha256'] and len(raw) == record['bytes'], 'Whole reviewed file ' + name)
    for folder_name, seal in pins['required_seals'].items():
        folder = ROOT / folder_name
        manifest = folder / 'MANIFEST.json'
        need(digest(manifest.read_bytes()) == seal, 'Whole accepted manifest ' + folder_name)
        members = load(manifest)['files']
        actual = {p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file() and p != manifest}
        need(actual == set(members), 'Complete accepted inventory ' + folder_name)
        for name, record in members.items():
            raw = (folder / name).read_bytes()
            need(digest(raw) == (record if isinstance(record, str) else record['sha256']), 'Whole inherited member ' + name)
            need(isinstance(record, str) or len(raw) == record['bytes'], 'Inherited member length ' + name)
    copies = load(HERE / 'COPIED_INPUTS.json')['files']
    actual_copies = {p.relative_to(HERE).as_posix() for folder in ['parents', 'vendor', 'provenance', 'coefficients']
                     for p in (HERE / folder).rglob('*') if p.is_file() or p.is_symlink()}
    need(actual_copies == set(copies), 'Complete exact copied-input inventory')
    for name, record in copies.items():
        raw = (HERE / name).read_bytes()
        need(not (HERE / name).is_symlink() and raw == (ROOT / record['source']).read_bytes() and digest(raw) == record['sha256']
             and len(raw) == record['bytes'], 'Whole exact accepted copy ' + name)
    return pins


def construct():
    pins = authenticate()
    copies = load(HERE / 'COPIED_INPUTS.json')['files']
    artifacts, maps, metrics, calibration = {}, {}, [], {}
    for case, stem, degree in CASES:
        local = 'parents/' + stem + '.json'
        parent_raw = (HERE / local).read_bytes()
        parent = load(HERE / local)
        need([r for r in parent['source'] if r[0] == 'Tp'] == [['Tp', '+', 'T', 'alpha']], 'Unique private Tp')
        need([r for r in parent['source'] if 'Tp' in r[2:]] == [['cT', '*', 'c', 'Tp']], 'Sole private consumer')
        rows = [['cT', '*', 'c', 'T'] if r[0] == 'cT' else list(r)
                for r in parent['source'] if r[0] != 'Tp']
        positions = {r[0]: i for i, r in enumerate(rows)}
        need(len(positions) == len(rows), 'Complete fresh output coordinates')
        map_rows = []
        for i, old in enumerate(parent['source']):
            action = 'deleted' if old[0] == 'Tp' else 'rewritten' if old[0] == 'cT' else 'retained'
            j = positions.get(old[0])
            map_rows.append({'old_index': i, 'old_row': old, 'action': action,
                             'new_index': j, 'new_row': None if j is None else rows[j]})
        theorem = 'research/ten-positive-unshift-t-' + ('square' if case.endswith('V2') else 'bv')
        parent_source = copies[local]['source']
        parent_folder = parent_source.split('/data/')[0] if '/data/' in parent_source else parent_source.rsplit('/', 1)[0]
        ordinary = {'path': theorem + '/PROPOSAL.md', 'manifest_sha256': pins['required_seals'][theorem]}
        ancestry = {'path': parent_source, 'sha256': digest(parent_raw),
                    'manifest_sha256': pins['required_seals'][parent_folder]}
        packet = deepcopy(parent)
        packet.update(name='unshift_T_' + parent['name'], source=rows, operations=len(rows),
                      operation_breakdown=dict(Counter(r[1] for r in rows)), exact_degree=degree,
                      proof='PROOF.md', proof_status=SCOPE, unshift_parent=ancestry, unshift_ordinary=ordinary)
        name = 'data/equation_' + case + '.json'
        artifacts[name] = encoded(packet)
        maps[case] = {'parent_local': local, 'rows': map_rows,
                      'new_to_old': [next(i for i, old in enumerate(parent['source']) if old[0] == r[0]) for r in rows],
                      'formal_parent_substitution': {'T': 'T-alpha'},
                      'positive_parent_to_new': {'T_new': 'T_old+alpha', 'other_inputs': 'fixed'},
                      'positive_new_to_parent': 'Decode refutation and rebuild canonical witnesses; no positive formal inverse.'}
        metrics.append({'case': case, 'file': name, 'positive_inputs': len(packet['witnesses']),
                        'operations': len(rows), 'operation_breakdown': packet['operation_breakdown'],
                        'degree_to_be_independently_collected': degree})
        calibration[case] = {'entire_parent': ancestry, 'ordinary_equivalence': ordinary,
                             'whole_coefficient_binding': packet['coefficient_binding'],
                             'canonical_requirements': ['R>3q', 'R=3 mod4', 'q^3 divides Y', 'fresh positive witnesses'],
                             'scope': 'Direct whole-parent and ordinary theorem composition; no fresh native/compiler/runtime theorem.'}
    artifacts['data/ROW_MAPS.json'] = encoded(maps)
    artifacts['data/METRICS.json'] = encoded(metrics)
    artifacts['data/CALIBRATION_BINDING.json'] = encoded(calibration)
    artifacts['data/INDEX.json'] = encoded({'schema': 'unshift_T_four_complete_graphs_v1',
        'producer_sha256': digest(Path(__file__).read_bytes()), 'source_pins_sha256': digest((HERE / 'SOURCE_PINS.json').read_bytes()),
        'files': {name: {'bytes': len(raw), 'sha256': digest(raw)} for name, raw in sorted(artifacts.items())}})
    return artifacts, metrics


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    artifacts, metrics = construct()
    output = args.output.resolve()
    protected = {(HERE / n).resolve() for n in set(load(HERE / 'SOURCE_PINS.json')['core']) |
                  {'SOURCE_PINS.json', 'HOLD_INVENTORY.json', 'MANIFEST.json'}}
    directories = [(HERE / n).resolve() for n in ['data', 'parents', 'vendor', 'provenance', 'coefficients']]
    need(not args.output.is_symlink() and output not in protected and not any(p == output or p in output.parents for p in directories), 'Fresh separate receipt path')
    need(not (HERE / 'data').is_symlink(), 'No generated-directory symlink')
    actual_data = {p.relative_to(HERE).as_posix() for p in (HERE / 'data').rglob('*') if p.is_file() or p.is_symlink()}
    need(actual_data == set(artifacts) if args.check else actual_data <= set(artifacts), 'No unindexed generated artifact')
    for name, raw in artifacts.items():
        path = HERE / name
        need(not path.is_symlink(), 'No artifact symlink')
        if args.check or path.exists():
            need(path.is_file() and path.read_bytes() == raw, 'Exact deterministic whole artifact ' + name)
    report = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
              'mode': 'pure deterministic rebuild' if args.check else 'four full literal graphs materialized',
              'artifacts': {name: {'bytes': len(raw), 'sha256': digest(raw)} for name, raw in sorted(artifacts.items())},
              'actual_metrics': metrics, 'no_optimizer_or_incoming_program': True}
    raw = encoded(report)
    need(not args.output.exists() or args.output.read_bytes() == raw, 'Reject a different existing receipt')
    if not args.check:
        for name, artifact in artifacts.items():
            path = HERE / name
            if not path.exists():
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(artifact)
    args.output.write_bytes(raw)
    print(raw.decode(), end='')


if __name__ == '__main__':
    main()
