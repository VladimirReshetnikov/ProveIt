#!/usr/bin/env python3
"""Optional, untrusted certificate discovery. Not needed to verify the theorem.
Requires g++ and a discoverable native Z3 shared library (not z3-solver Python).
Outputs new data in a user-selected directory; does not overwrite the supplied data.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ProcessPoolExecutor
import json
from pathlib import Path
import subprocess
import time
from attack import predecessor


def solve_job(job):
    m, n, key, timeout = job
    columns = [a for a in range(1 << m) if key & (1 << a)]
    target = {(i, j) for j, a in enumerate(columns)
              for i in range(m) if a & (1 << i)}
    d = predecessor(target, m, n, timeout=timeout, full_support=True)
    if d['status'] != 'sat':
        raise RuntimeError(f'No certificate obtained: m={m}, n={n}, key={key}, {d}')
    before = {tuple(x) for x in d['P']}
    if {i for i, _ in before} != set(range(m)) or {j for _, j in before} != set(range(n)):
        raise RuntimeError('Returned predecessor does not have full support')
    return {'m': m, 'n': n, 'key': key, 'columns': columns,
            'f': d['f'], 'g': d['g'],
            'predecessor': [sum(1 << i for i in range(m) if (i, j) in before)
                            for j in range(n)]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--timeout-ms', type=int, default=30000)
    parser.add_argument('--rows', type=int, nargs='+', default=list(range(1, 7)))
    args = parser.parse_args()
    if args.jobs < 1 or args.timeout_ms < 1 or any(not 1 <= m <= 6 for m in args.rows):
        parser.error('positive jobs/timeout and row counts in 1..6 required')
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if (out/'certificates.txt').exists() or (out/'certificates.jsonl').exists():
        parser.error('output already contains certificates; choose a fresh directory')
    start = time.perf_counter()
    binary = out/'enumerate'
    source = Path(__file__).resolve().parent/'enumerate.cpp'
    subprocess.run(['g++', '-O3', '-std=c++17', str(source), '-o', str(binary)], check=True)
    jobs = []
    for m in sorted(set(args.rows)):
        listing = out/f'classes{m}.txt'
        with (out/f'enumerate{m}.log').open('w') as log:
            subprocess.run([str(binary), str(m), str(listing)], stderr=log, check=True)
        for line in listing.read_text().splitlines():
            mm, n, key, hard = map(int, line.split())
            if hard:
                jobs.append((mm, n, key, args.timeout_ms))
    records = []
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        for d in pool.map(solve_job, jobs, chunksize=1):
            records.append(d)
            if len(records) % 256 == 0:
                print(f'{len(records)}/{len(jobs)} positive certificates', flush=True)
    records.sort(key=lambda d: (d['m'], d['n'], d['key']))
    with (out/'certificates.jsonl').open('w') as js, (out/'certificates.txt').open('w') as text:
        text.write('# m n family_key | f | g | predecessor_column_masks\n')
        for d in records:
            js.write(json.dumps(d, separators=(',', ':'))+'\n')
            fields = [d['m'], d['n'], d['key']]+d['f']+d['g']+d['predecessor']
            text.write(' '.join(map(str, fields))+'\n')
    print(f'Generated {len(records)} certificates in {time.perf_counter()-start:.3f} seconds.')
    print('These are search outputs. Run src/verify_all.cpp on the generated text file.')
    if sorted(set(args.rows)) != list(range(1, 7)):
        print('Only selected row counts were generated; this is not a complete proof database.')


if __name__ == '__main__':
    main()
