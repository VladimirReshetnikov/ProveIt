#!/usr/bin/env python3
"""Reproduce three source-audit corruption controls on the current release.

Only the independent verify_source module is imported from this package.
No equation builder is imported or run. All corrupted files exist only in a
TemporaryDirectory. The only persistent output is the requested JSON receipt.
The deterministic receipt is identical under ordinary and optimized Python.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tempfile

import verify_source


def require(condition, message):
    if not condition:
        raise ValueError(message)


def run(package):
    inputs = (
        'source/horn_shared_source.json',
        'equations/local_row.json',
        'equations/semantic_certificate.json',
    )
    positive = verify_source.run(package)
    require(positive['status'] == 'PASS', 'Unmodified source did not pass')
    original = (package / inputs[2]).read_bytes()
    controls = []

    with tempfile.TemporaryDirectory(prefix='con-zfc-source-controls-') as directory:
        scratch = Path(directory)
        for name in inputs:
            destination = scratch / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(package / name, destination)
        require(verify_source.run(scratch)['status'] == 'PASS',
                'Copied unmodified source did not pass')
        target = scratch / inputs[2]

        def check(label, mutate, expected_reason):
            data = json.loads(original)
            mutate(data)
            target.write_text(json.dumps(data, separators=(',', ':')) + '\n')
            try:
                verify_source.run(scratch)
            except ValueError as error:
                reason = str(error)
                require(expected_reason in reason,
                        'Control rejected for an unexpected reason: ' + reason)
                controls.append({'mutation': label, 'status': 'REJECTED',
                                 'reason': reason})
            else:
                raise ValueError('Source corruption was accepted: ' + label)

        def wrong_schema_bound(data):
            bounds = data['source_binding']['coordinate_bounds']
            require(bounds[0] != bounds[4], 'Schema-bound mutation would be vacuous')
            bounds[0] = bounds[4]

        def signed_majorant(data):
            source = data['source_binding']
            require(source['upper_e'] != source['encoded_e'],
                    'Majorant mutation would be vacuous')
            source['upper_e'] = source['encoded_e']

        def missing_horizon_guard(data):
            index = data['variable_names'].index('N minus one')
            require(index not in data['unrestricted_inputs'],
                    'Horizon-domain mutation would be vacuous')
            data['unrestricted_inputs'].append(index)

        check('Replace the first schema-parameter bound N by y',
              wrong_schema_bound, 'heterogeneous N/y/U bounds')
        check('Replace the absolute upper bound by the signed encoded row',
              signed_majorant, 'absolute-circuit majorant')
        check('Remove nonnegativity of the positive horizon predecessor',
              missing_horizon_guard, 'unconditional positive exponent')

    require(len(controls) == 3, 'Incomplete corruption inventory')
    return {
        'status': 'PASS',
        'unmodified_source': 'PASS',
        'copied_unmodified_source': 'PASS',
        'controls': controls,
        'sha256': {name: hashlib.sha256((package / name).read_bytes()).hexdigest()
                   for name in inputs},
        'independent_checker_sha256': hashlib.sha256(
            Path(verify_source.__file__).read_bytes()).hexdigest(),
        'scope': ('Three meaningful source/domain corruption controls on the current '
                  'literal certificate. No builder, halting search, or consistency '
                  'decision is performed. All checks use explicit exceptions.'),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path,
                        default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run(args.package)
    destination = args.output or args.package / 'checks' / 'SOURCE_NEGATIVE_CONTROLS.json'
    destination.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(result, indent=2, sort_keys=True) + '\n'
    destination.write_text(payload)
    print(payload)


if __name__ == '__main__':
    main()
