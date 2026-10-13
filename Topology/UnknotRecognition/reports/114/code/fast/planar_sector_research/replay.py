"""Replay retained coverage samples using only the independent checker.

This module does not import the sparse builder, polygon producer or enumerator.
The optional output is a small, deterministic machine-readable replay record.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path

from fastunknot.sector_planar_verify import verify_planar_sector_certificate


def replay(path):
    data = path.read_bytes()
    bundle = json.loads(data)
    if bundle.get('schema') != 'planar-sector-coverage-samples-v1':
        raise ValueError('unexpected coverage-sample schema')
    records = []
    for sample in bundle['records']:
        stats = {}
        accepted = verify_planar_sector_certificate(
            sample['triangulation'], sample['certificate'], stats=stats)
        if not accepted:
            raise AssertionError(('coverage certificate rejected', sample['source_id']))
        records.append(dict(
            source_id=sample['source_id'],
            matching_dimension=sample['certificate']['matching_dimension'],
            section_dimension=sample['certificate']['section_dimension'],
            accepted=True, stats=stats))
    return dict(schema='planar-sector-coverage-replay-v1',
                input_sha256=sha256(data).hexdigest(),
                all_accepted=True, count=len(records), records=records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificates', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    answer = replay(args.certificates)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(answer, indent=2, sort_keys=True) + '\n')
    print(json.dumps(answer, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
