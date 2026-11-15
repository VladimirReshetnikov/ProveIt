#!/usr/bin/env python3
"""Replay a finite fold-search batch using only this package and compiled engines."""
import argparse
import concurrent.futures
import hashlib
import json
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--engine', choices=['noncircular', 'recursive_folds'], default='noncircular')
    ap.add_argument('--radius', type=int, default=7)
    ap.add_argument('--fuel', type=int, default=31)
    ap.add_argument('--cases', nargs='*', help='Input names; default is the thirteen incoming194 tables')
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--output', type=Path, default=HERE/'reruns')
    args = ap.parse_args()
    manifest = json.loads((HERE/'SOURCE_TABLES.json').read_text())
    selected = [e for e in manifest if e['name'] in args.cases] if args.cases else [e for e in manifest if e['batch13']]
    if args.cases and set(args.cases) != {e['name'] for e in selected}:
        ap.error('Unknown case name; inspect SOURCE_TABLES.json')
    binary = HERE/args.engine
    if not binary.exists():
        ap.error('Compile '+args.engine+'.cpp as described in README.md')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)

    def run(e):
        source = HERE/e['input']
        if hashlib.sha256(source.read_bytes()).hexdigest() != e['sha256']:
            raise ValueError('Input SHA256 mismatch: '+e['name'])
        stem = f"{e['name']}_{args.engine}_r{args.radius}_f{args.fuel}"
        prefix = output/stem
        command = [str(binary), str(source)]
        if args.engine == 'noncircular':
            command.append(str(prefix))
        command += [str(args.radius), str(args.fuel)]
        before = time.perf_counter()
        with prefix.with_suffix('.log').open('w') as out, prefix.with_suffix('.stderr').open('w') as err:
            process = subprocess.run(command, stdout=out, stderr=err)
        record = {
            'name':e['name'], 'engine':args.engine, 'radius':args.radius,
            'fuel':args.fuel, 'returncode':process.returncode,
            'seconds':time.perf_counter()-before,
            'matches':prefix.with_suffix('.log').read_text().splitlines(),
            'stderr':prefix.with_suffix('.stderr').read_text(),
            'source_sha256':e['sha256'], 'command':command,
        }
        prefix.with_suffix('.json').write_text(json.dumps(record, indent=2)+'\n')
        if process.returncode:
            raise RuntimeError(record['stderr'])
        print(json.dumps({k:v for k,v in record.items() if k not in ('command', 'source_sha256')}), flush=True)
        return record

    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        records = list(pool.map(run, selected))
    name = f'{args.engine}_r{args.radius}_f{args.fuel}_batch.json'
    (output/name).write_text(json.dumps(records, indent=2)+'\n')


if __name__ == '__main__':
    main()
