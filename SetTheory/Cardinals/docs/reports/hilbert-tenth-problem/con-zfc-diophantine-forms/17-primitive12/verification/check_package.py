#!/usr/bin/env python3
"""Authenticate and structurally check the delivered research package.

This is not a proof of compiler semantics, K215 nonhalting, or consistency.
All validations remain active under python -O. No network access is used.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = {
    'arithmetic/primitive12/generated/primitive12_system.json': (12, 163, [7, 2, 2592]),
    'arithmetic/primitive12/generated/primitive12_product.json': (12, 167, 2601),
    'arithmetic/primitive12/generated/primitive12_sos.json': (12, 170, 5184),
    'arithmetic/integer26/generated/integer26_system.json': (26, 225, [13, 4, 5248]),
    'arithmetic/integer26/generated/integer26_product.json': (26, 229, 5265),
    'arithmetic/integer26/generated/integer26_sos.json': (26, 232, 10496),
    'arithmetic/integer27/integer27_product139.json': (27, 139, 1116),
    'arithmetic/baseline67.json': (15, 67, 155),
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads((ROOT / path).read_text())


def check_circuit(path, expectation):
    packet = load(path)
    variables, operations, degree = expectation
    inputs = packet['witnesses'] + packet['fixed_numerals']
    require(len(inputs) == len(set(inputs)), f'{path}: duplicate input')
    known = set(inputs)
    counts = Counter()
    for name, op, left, right in packet['source']:
        require(name not in known, f'{path}: duplicate gate {name}')
        require(op in ('+', '-', '*'), f'{path}: unsupported operation')
        require(all(isinstance(x, int) or x in known for x in (left, right)),
                f'{path}: forward/unknown reference at {name}')
        known.add(name)
        counts[op] += 1
    if 'output' in packet:
        outputs = [packet['output']]
    else:
        outputs = [x for pair in packet['comparisons'] for x in pair]
    require(all(isinstance(x, int) or x in known for x in outputs),
            f'{path}: unknown output')
    live = {x for x in outputs if isinstance(x, str)}
    for name, _, left, right in reversed(packet['source']):
        if name in live:
            live.update(x for x in (left, right) if isinstance(x, str))
    require(set(inputs).issubset(live), f'{path}: unused input')
    require(all(row[0] in live for row in packet['source']), f'{path}: dead gate')
    require(len(packet['witnesses']) == variables, f'{path}: variable count')
    require(len(packet['source']) == operations == packet['ledger']['operations'],
            f'{path}: operation count')
    ledger = packet['ledger']
    require(ledger.get('multiplications', ledger.get('M')) == counts['*'],
            f'{path}: multiplication count')
    require(ledger.get('additions_subtractions', ledger.get('A')) == counts['+']+counts['-'],
            f'{path}: addition count')
    claimed = packet.get('exact_degree', packet.get('residual_exact_degrees'))
    require(claimed == degree, f'{path}: degree metadata')
    require(packet['fixed_numerals'] == ['Bm1', 'Kconstant', 'MC', 'MF'],
            f'{path}: coefficient-port convention')
    return {'path': path, 'variables': variables, 'operations': operations,
            'multiplications': counts['*'], 'additions_subtractions': counts['+']+counts['-'],
            'degree_metadata': degree, 'all_inputs_and_gates_live': True}


def module_from_file(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_generation():
    checks = 0
    for label, directory in (('primitive12', 'primitive12'), ('integer26', 'integer26')):
        module = module_from_file('audit_' + label, f'arithmetic/{directory}/build_{label}.py')
        for packet in module.build():
            relative = f'arithmetic/{directory}/generated/{packet["name"]}.json'
            require(packet == load(relative), f'Generator/artifact mismatch: {relative}')
            checks += 1
    module = module_from_file('audit_integer27', 'arithmetic/integer27/build_integer27.py')
    require(module.build() == load('arithmetic/integer27/integer27_product139.json'),
            'Generator/artifact mismatch: integer27')
    return checks + 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-manifest', action='store_true',
                        help='Permit regenerated receipts to differ from the delivered snapshot.')
    parser.add_argument('--out', type=Path, help='Optionally save the structural-check report.')
    args = parser.parse_args()
    pins = load('SOURCE_PINS.json')
    require(pins['snapshot'] == 'f0ae4e0991ca44a7bb4e5671d42e33d775e48035',
            'Unexpected repository snapshot')
    for entry in pins['inherited_files']:
        require(digest(ROOT / entry['local']) == entry['sha256'],
                'Inherited source hash mismatch: ' + entry['local'])
        data = (ROOT / entry['local']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(blob == entry['git_blob_sha1'], 'Pinned Git blob mismatch: ' + entry['local'])
    constants = load('compiler/PRUNED_T4_CONSTANTS.json')
    for file_key, hash_key in (('machine_table', 'machine_table_sha256'),
                               ('transition_projection', 'transition_projection_sha256')):
        require(digest(ROOT / 'compiler' / constants[file_key]) == constants[hash_key],
                'Compiler literal data hash mismatch')
    tiles = constants['tiles']
    require(digest(ROOT / 'compiler' / tiles['file']) == tiles['sha256'], 'Tile-list hash mismatch')
    require(len(load('compiler/' + tiles['file'])) == tiles['count'] == 5252, 'Tile count mismatch')
    require((ROOT/'machine/k215.tm').read_bytes() == (ROOT/'compiler/k215.tm').read_bytes(),
            'Machine copies differ')
    instance = load('INSTANCE.json')
    require(instance['coefficient_binding'] == constants['binding'], 'Instance binding mismatch')
    require(instance['coefficient_recipe'] == 'compiler/PRUNED_T4_CONSTANTS.json',
            'Unexpected coefficient recipe')
    circuits = [check_circuit(path, expected) for path, expected in EXPECTED.items()]
    regenerated = check_generation()
    manifest_files = 0
    if not args.skip_manifest:
        manifest = ROOT / 'SHA256SUMS'
        require(manifest.exists(), 'SHA256SUMS absent; use --skip-manifest only during assembly')
        for line in manifest.read_text().splitlines():
            expected, relative = line.split('  ', 1)
            path = (ROOT / relative).resolve()
            require(ROOT in path.parents, 'Manifest path escapes package')
            require(path.is_file() and digest(path) == expected, 'Package hash mismatch: ' + relative)
            manifest_files += 1
    report = {
        'status': 'PASS', 'repository_snapshot': pins['snapshot'],
        'inherited_source_hashes': len(pins['inherited_files']),
        'coefficient_binding': constants['binding'],
        'tile_count': tiles['count'], 'circuits': circuits,
        'generated_circuits_recomputed_in_memory': regenerated,
        'package_manifest_files_checked': manifest_files,
        'scope': 'Source authentication and circuit structure. Degree metadata is not a proof of degree; '
                 'the article provides leading-form proofs. No halting, consistency, or formalization claim.'
    }
    if args.out:
        args.out.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
