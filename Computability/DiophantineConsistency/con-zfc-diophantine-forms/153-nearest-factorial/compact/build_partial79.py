#!/usr/bin/env python3
"""Reproduce the 79-operation evaluator from its retained 80-operation source.

Default and --check modes are read-only and compare both generated JSON files
byte for byte with this release. --output-dir DIR writes the two reproduced
JSON files elsewhere. Only the Python standard library is required.

The proof is the exact identity (D*Y)*k = D*(k*Y), with all other gates
unchanged. The modular comparisons are supplemental regression checks.
"""
import argparse
import hashlib
import json
from collections import Counter
from copy import deepcopy
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'upstream' / 'equation_80_382_partial.json'
SOURCE_SHA256 = 'd64444dc78a1d48020ffc894a6d31592a1446705998290b3e0bc9a6fcf8ea6f2'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def evaluate(doc, values, modulus):
    env = dict(values)
    for name, op, a, b in doc['source']:
        a = a if type(a) is int else env[a]
        b = b if type(b) is int else env[b]
        env[name] = (a + b if op == '+' else a - b if op == '-' else a * b) % modulus
    return env[doc['output']]


def generate():
    raw = SOURCE.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    require(digest == SOURCE_SHA256, 'The retained source bytes differ from the reviewed parent')
    old = json.loads(raw)
    rows = {row[0]: row for row in old['source']}
    require(len(rows) == len(old['source']), 'Duplicate parent register')
    require(rows['kY'] == ['kY', '*', 'k', 'Y'], 'kY definition changed')
    require(rows['V0'] == ['V0', '*', 'D', 'Y'], 'V0 definition changed')
    require(rows['V0k'] == ['V0k', '*', 'V0', 'k'], 'V0k definition changed')
    require(sum('V0' in row[2:] for row in old['source']) == 1,
            'V0 has another use')
    require(old['output'] != 'V0', 'The deleted register is the output')
    require(old['exact_degree'] == 382 and old['operations'] == 80,
            'Unexpected parent metrics')

    new = deepcopy(old)
    new['source'] = [(['V0k', '*', 'D', 'kY'] if row[0] == 'V0k' else row)
                     for row in old['source'] if row[0] != 'V0']
    new['name'] = 'partial_q2_shared_kY_79_382'
    new['operations'] = len(new['source'])
    new['operation_breakdown'] = dict(Counter(row[1] for row in new['source']))
    new['exact_degree'] = 382
    new['proof'] = 'PROOF.md'
    new['parent'] = 'parent80.json'
    new['parent_sha256'] = digest
    new['generation'] = 'Delete the single-use V0=D*Y register; replace V0k=V0*k by V0k=D*kY. Every other row is identical.'
    require(new['operations'] == 79, 'Expected 79 operations')
    require(new['operation_breakdown'] == {'*': 47, '+': 17, '-': 15},
            'Unexpected operation breakdown')

    for row in new['source']:
        if row[0] != 'V0k':
            require(row == rows[row[0]], 'An unrelated row changed')
    for key in ['domain', 'witnesses', 'fixed_numerals', 'coefficient_binding', 'output']:
        require(new[key] == old[key], 'Changed semantic field: ' + key)

    leaves = new['witnesses'] + new['fixed_numerals']
    require(len(leaves) == len(set(leaves)), 'Duplicate input leaf')
    known = set(leaves)
    dependencies = {}
    for name, op, a, b in new['source']:
        require(name not in known, 'Duplicate register')
        require(op in ['+', '-', '*'], 'Illegal operation')
        require(all(type(value) is int or value in known for value in (a, b)),
                'Broken topology')
        known.add(name)
        dependencies[name] = [value for value in (a, b) if isinstance(value, str)]
    live, stack = set(), [new['output']]
    while stack:
        name = stack.pop()
        if name not in live:
            live.add(name)
            stack.extend(dependencies.get(name, []))
    require(live == known, 'Dead wire, variable or fixed coefficient')

    # The preceding gate identities prove equality over the integer polynomial
    # ring, for all inputs and all coefficient values. Finite evaluations below
    # only supplement that proof; they do not establish degree or calibration.
    tests = 0
    for modulus in [2147483647, 2305843009213693951]:
        for t in range(20):
            values = {name: ((j + 3) ** 3 + 19*t - 7) % modulus
                      for j, name in enumerate(leaves)}
            require(evaluate(new, values, modulus) == evaluate(old, values, modulus),
                    'Supplemental modular output disagreement')
            tests += 1

    artifacts = {'parent80.json': raw,
                 'equation79_degree382.json': (json.dumps(new, indent=2) + '\n').encode('utf-8')}
    receipt = {'status': 'PASS', 'parent_sha256': digest,
               'operations': 79, 'operation_breakdown': new['operation_breakdown'],
               'exact_degree': 382,
               'degree_justification': 'The entire polynomial is identical to the authenticated parent.',
               'symbolic_identity': '(D*Y)*k = D*(k*Y)',
               'all_other_gates_literal': True, 'all_variables_ports_gates_live': True,
               'whole_coefficient_binding_preserved': True,
               'supplemental_modular_evaluations': tests,
               'artifact_sha256': {name: hashlib.sha256(data).hexdigest()
                                   for name, data in artifacts.items()}}
    return artifacts, receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true',
                      help='Compare generated bytes with the release files (the default)')
    mode.add_argument('--output-dir', type=Path,
                      help='Write the reproduced JSON pair into a different directory')
    args = parser.parse_args()
    artifacts, receipt = generate()
    if args.output_dir is None:
        for name, data in artifacts.items():
            require((ROOT / name).read_bytes() == data,
                    'Byte-identical reproduction failed: ' + name)
        receipt['mode'] = 'read-only byte comparison'
        receipt['byte_identical_files'] = list(artifacts)
    else:
        destination = args.output_dir.resolve()
        require(destination != ROOT.resolve(),
                '--output-dir must differ from the retained compact directory')
        # A symlink must not turn an elsewhere build into an overwrite here.
        protected = {(ROOT / name).resolve() for name in artifacts}
        require(all((destination / name).resolve() not in protected for name in artifacts),
                'An output file resolves to a retained release artifact')
        destination.mkdir(parents=True, exist_ok=True)
        for name, data in artifacts.items():
            (destination / name).write_bytes(data)
        receipt['mode'] = 'write reproduced JSON pair elsewhere'
        receipt['output_directory'] = str(destination)
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
