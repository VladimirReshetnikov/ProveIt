#!/usr/bin/env python3
"""Recover the complete routed245 delivery outside the repository; execute nothing."""
import argparse
import io
import json
from pathlib import Path
import subprocess
import zipfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    if output.exists() or output.is_relative_to(repo) or repo.is_relative_to(output):
        parser.error('Output must be a new directory outside the repository.')
    host = repo / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
    mapping = json.loads((host / 'data/intake-164-placement.json').read_text())
    raw = subprocess.check_output([
        'git', '-C', str(repo), 'show', mapping['arrival'] + ':' + mapping['archive']])
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        for member in archive.infolist():
            path = Path(member.filename)
            if path.is_absolute() or '..' in path.parts or (member.external_attr >> 16) & 0o170000 == 0o120000:
                raise ValueError('Unsafe archive member: ' + member.filename)
        # Compare delivered payloads directly, without interpreting manifests.
        for item in mapping['placements']:
            name = mapping['wrapper'] + '/' + item['delivered']
            if (repo / item['target']).read_bytes() != archive.read(name):
                raise ValueError('Placed payload differs: ' + item['target'])
        archive.extractall(output)
    files = [p for p in output.rglob('*') if p.is_file()]
    if len(files) != mapping['counts']['payloads']:
        raise ValueError('Unexpected recovered payload count')
    print(json.dumps(dict(
        status='PASS_RECOVERY_ONLY', arrival=mapping['arrival'],
        package=str(output / mapping['wrapper']), recovered_files=len(files),
        placed_pairs_compared=len(mapping['placements']),
        checksum_manifests_checked=False, programs_executed=False), indent=2))


if __name__ == '__main__':
    main()
