#!/usr/bin/env python3
"""Replay bounded negative searches from frozen complete TM tables."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
PRIMARY_SHA = 'e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'


def table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        if (q, b) in rows or b not in (0, 1) or w not in (0, 1) or d not in ('L', 'R'):
            raise ValueError(f'Invalid literal row in {path}')
        rows[q, b] = w, d, n
    controls = {q for q, b in rows}
    if len(controls) != 194 or set(rows) != {(q, b) for q in controls for b in (0, 1)}:
        raise ValueError(f'Not a complete 194-state table: {path}')
    if 74 not in controls or 254 in controls or {n for w, d, n in rows.values()} - controls != {254}:
        raise ValueError(f'Invalid start/halt controls: {path}')
    return rows


def encode(rows):
    return ''.join(f'{q} {b} {w} {d} {n}\n'
                   for (q, b), (w, d, n) in sorted(rows.items()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--all', action='store_true', help='Repeat the full corpus and neutral-rewrite suites')
    parser.add_argument('--jobs', type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    args.output.mkdir(parents=True, exist_ok=True)

    primary = ROOT / 'inputs/primary.native.tm'
    primary_rows = table(primary)
    if hashlib.sha256(primary.read_bytes()).hexdigest() != PRIMARY_SHA:
        raise ValueError('Primary input hash mismatch')
    corpus = sorted((ROOT / 'inputs/corpus').glob('*.tm'))
    if len(corpus) != 530:
        raise ValueError('Expected the frozen 530-table corpus')
    for path in corpus:
        table(path)
        if hashlib.sha256(path.read_bytes()).hexdigest() != path.stem:
            raise ValueError(f'Corpus input hash mismatch: {path}')

    compiler = os.environ.get('CXX') or shutil.which('g++') or shutil.which('c++')
    if not compiler:
        raise SystemExit('A C++17 compiler is required; set CXX if necessary.')
    records = []
    with tempfile.TemporaryDirectory(prefix='pa194_physical_search_') as tmp_name:
        tmp = Path(tmp_name)
        engines = ['local_search', 'recursive_folds']
        if args.all:
            engines += ['edge_bypass', 'multisync', 'edge_multisync']
        for name in engines:
            subprocess.run([compiler, '-O1', '-std=c++17', str(ROOT / 'code' / (name + '.cpp')),
                            '-o', str(tmp / name)], check=True)

        tasks = [('primary-local-radius9', 'local_search', primary, 9, 128),
                 ('primary-recursive-radius7', 'recursive_folds', primary, 7, 64)]
        for stem in ('AX11H_SF', 'LC_AX11H_SF'):
            path = ROOT / 'inputs' / (stem + '.native.tm')
            table(path)
            tasks.append((stem + '-recursive-radius7', 'recursive_folds', path, 7, 64))

        if args.all:
            regenerated = tmp / 'neutral_candidates.txt'
            neutral_check = subprocess.run(
                [str(tmp / 'local_search'), str(primary), '7', '128', str(regenerated)],
                text=True, capture_output=True, check=True)
            if set(regenerated.read_text().splitlines()) != set(
                    (ROOT / 'receipts/neutral_candidates.txt').read_text().splitlines()):
                raise ValueError('Regenerated neutral-row certificate list differs')
            records.append({'name': 'neutral-rewrite-certificate-regeneration',
                            'engine': 'local_search', 'table_sha256': PRIMARY_SHA,
                            'radius': 7, 'replacement_step_bound': 128,
                            'returncode': neutral_check.returncode,
                            'candidate_reductions': neutral_check.stdout,
                            'diagnostics': neutral_check.stderr})
            for path in corpus:
                for engine in ('local_search', 'edge_bypass', 'multisync'):
                    tasks.append((engine + '-' + path.stem, engine, path, 5, 64))
            for line in (ROOT / 'receipts/neutral_candidates.txt').read_text().splitlines():
                q, b, w, d, n, length = line.split()
                q, b, w, n = map(int, (q, b, w, n))
                rows = dict(primary_rows)
                rows[q, b] = w, d, n
                tag = f'neutral-{q}-{b}-{w}{d}{n}'
                path = tmp / (tag + '.tm')
                path.write_text(encode(rows))
                table(path)
                tasks.append((tag, 'local_search', path, 5, 64))
            for path in sorted((ROOT / 'inputs/closed').glob('*.tm')):
                table(path)
                for engine in ('recursive_folds', 'edge_multisync'):
                    tasks.append((path.stem + '-' + engine, engine, path, 5, 64))

        def run(task):
            name, engine, path, radius, bound = task
            result = subprocess.run([str(tmp / engine), str(path), str(radius), str(bound)],
                                    text=True, capture_output=True)
            return {'name': name, 'engine': engine,
                    'table_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                    'radius': radius, 'replacement_step_bound': bound,
                    'returncode': result.returncode,
                    'candidate_reductions': result.stdout,
                    'diagnostics': result.stderr}

        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for record in pool.map(run, tasks):
                records.append(record)
                if record['returncode']:
                    (args.output / 'replay.json').write_text(json.dumps(records, indent=2) + '\n')
                    raise RuntimeError(f"Search execution failed: {record['name']}")

    result = {'searches_completed': len(records),
              'reductions_found': sum(bool(r['candidate_reductions']) for r in records),
              'scope': 'Bounded searches only; no global state lower bound and no absolute arithmetic calibration',
              'records': records}
    (args.output / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}, indent=2))


if __name__ == '__main__':
    main()
