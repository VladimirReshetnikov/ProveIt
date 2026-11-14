#!/usr/bin/env python3
"""Recompute all table classes in the pinned repository's historical catalogue."""
from pathlib import Path
import argparse
import csv
import importlib.util
import json
import subprocess

PIN = '4be5c6e3a10292a7466f5d3687e3b39615ff049b'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--output', type=Path, default=Path.cwd() / 'official-catalogue-replay.json')
    args = ap.parse_args()
    repo = args.repo.resolve()
    assert subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip() == PIN
    directory = repo / 'Computability/BusyBeaver/Research/PA/docs'
    spec = importlib.util.spec_from_file_location('pinned_machine_classes', directory / 'machine_classes.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    records = []
    with (directory / 'MACHINES.tsv').open() as stream:
        for row in csv.DictReader(stream, delimiter='\t'):
            data = module.classify((repo / row['kept_file']).read_bytes())
            assert data['table'] == row['table_class'], row['kept_file']
            records.append(dict(original_class=row['class'], table_class=data['table'],
                                kept_file=row['kept_file'], states=data['states'],
                                reachable=data['reachable']))
    assert len(records) == 535
    result = dict(status='PASS', snapshot=PIN, count=len(records), records=records)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: all 535 historical catalogue table hashes agree.')


if __name__ == '__main__':
    main()
