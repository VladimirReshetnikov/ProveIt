#!/usr/bin/env python3
"""Optional bounded local-merge searches. No result is a state lower bound."""
import argparse, hashlib, json, os, subprocess, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE_SHA = 'b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
SITES_SHA = '0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline219', required=True, type=Path)
    ap.add_argument('--output-dir', required=True, type=Path)
    ap.add_argument('--compiler', default=os.environ.get('CXX', 'g++'))
    a = ap.parse_args()
    out = a.output_dir.resolve()
    if out.exists() and any(out.iterdir()):
        raise ValueError('Output directory must initially be empty')
    out.mkdir(parents=True, exist_ok=True)
    table = a.baseline219.resolve() / 'machine/k219.native.tm'
    sites = a.baseline219.resolve() / 'machine/sites219.json'
    assert hashlib.sha256(table.read_bytes()).hexdigest() == BASE_SHA
    assert hashlib.sha256(sites.read_bytes()).hexdigest() == SITES_SHA
    rows = json.loads(sites.read_text())
    site_text = out / 'sites.txt'
    site_text.write_text(''.join(f'{p} {op} {arg if arg is not None else 0}\n'
                                 for p, op, arg in rows))
    jobs = []
    def run(name, command):
        print(name, flush=True)
        start = time.monotonic()
        log = out / (name + '.log')
        with log.open('w') as f:
            subprocess.run(list(map(str, command)), stdout=f,
                           stderr=subprocess.STDOUT, check=True)
        jobs.append(dict(name=name, seconds=time.monotonic()-start,
                         log=log.name, last_lines=log.read_text().splitlines()[-2:]))
    for name in ['sample_windows64', 'window_fold', 'window_fold64', 'headshift_fold1']:
        run('compile_' + name, [a.compiler, '-O3', '-std=c++17', HERE / (name + '.cpp'),
                               '-o', out / name])
    run('sample20', [out/'sample_windows64', table, site_text, out/'samples20.txt', 20])
    run('merge7_overapproximation', [out/'window_fold', table, out/'merge7', 7])
    run('merge20_samples', [out/'window_fold64', table, out/'merge20', 20, out/'samples20.txt'])
    run('headshift_one_row20', [out/'headshift_fold1', table, out/'headshift20', 20, out/'samples20.txt'])
    receipt = dict(status='BOUNDED_SEARCHES_COMPLETED', phases=jobs,
                   scope='Restricted heuristic searches with finite local-join bounds; no completeness, minimality, or state-lower-bound claim.')
    (out/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(receipt['status'])

if __name__ == '__main__':
    main()
