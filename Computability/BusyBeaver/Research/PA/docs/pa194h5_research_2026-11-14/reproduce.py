#!/usr/bin/env python3
"""Replay the delivered finite certificates without changing their recorded files.

Python 3.10+ standard library. Optional --bootstrap additionally needs C++17.
This is not a proof-assistant kernel check of the ordinary PA calibration.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def check_hashes():
    count = 0
    for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
        expected, name = line.split('  ', 1)
        path = ROOT / name
        assert path.is_file(), name
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        assert actual == expected, f'Checksum mismatch: {name}'
        count += 1
    return count

def main():
    assert __debug__ and not sys.flags.optimize, 'Run without Python -O.'
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--checksums-only', action='store_true')
    p.add_argument('--h5-only', action='store_true')
    p.add_argument('--bootstrap', action='store_true', help='Also replay the two finite C++ startup searches')
    p.add_argument('--output', type=Path, default=ROOT / 'replay_results.json')
    a = p.parse_args()
    hashes = check_hashes()
    print(f'PASS: {hashes} delivered checksums', flush=True)
    if a.checksums_only:
        return
    result = {'status': 'PASS', 'verified_manifest_files': hashes,
              'kernel_checked': False,
              'scope': 'Finite and symbolic executable certificates; the ordinary mathematical PA calibration is in the report.'}
    with tempfile.TemporaryDirectory(prefix='pa_conpa_replay_') as tmp:
        temp = Path(tmp)
        def run(tag, *args):
            print(f'Checking {tag}...', flush=True)
            log = temp / (tag + '.log')
            with log.open('w') as out:
                code = subprocess.run([sys.executable, *map(str,args)], cwd=ROOT,
                                      stdout=out, stderr=subprocess.STDOUT).returncode
            if code:
                print(log.read_text(), file=sys.stderr)
                raise RuntimeError(f'{tag} failed with exit status {code}')
        run('H5', ROOT/'verify_all.py', '--frontier', ROOT/'comparison/frontier_tables',
            '--output', temp/'H5.json')
        result['H5'] = json.loads((temp/'H5.json').read_text())
        if not a.h5_only:
            sparse = ROOT/'research/sparse'
            generated = temp/'even195HX'
            run('even195_construction', sparse/'verify_even195_hx.py', sparse/'primary',
                '--out', generated)
            for name in ['even195HX.tm', 'even195HX.native.tm', 'even195HX.labels.json',
                         'source.sites.json', 'source.instructions.json', 'seed_bridge.json']:
                assert (generated/name).read_bytes() == (sparse/'even195HX'/name).read_bytes(), name
                assert (sparse/'even195HX'/name).read_bytes() == (sparse/'independent/inputs'/name).read_bytes(), name
            run('even195_independent', sparse/'independent/check.py',
                '--output', temp/'even195_independent')
            run('even195_source_delta', sparse/'independent/check_source_delta.py',
                '--output', temp/'even195_source_delta.json')
            run('sparse_source', sparse/'check_sparse_source.py', '--construction', sparse/'primary')
            run('sparse_arithmetic', sparse/'sparse_scheduler.py')
            result['even195_construction'] = json.loads((generated/'verification.json').read_text())
            result['even195_independent'] = json.loads((temp/'even195_independent/receipt.json').read_text())
            result['even195_source_delta'] = json.loads((temp/'even195_source_delta.json').read_text())
            result['sparse_source'] = json.loads((temp/'sparse_source.log').read_text())
            result['sparse_arithmetic'] = json.loads((temp/'sparse_arithmetic.log').read_text())
        if a.bootstrap:
            run('bootstrap', ROOT/'research/reduction/reproduce_bootstrap.py',
                '--output', temp/'bootstrap')
            result['bootstrap_replay'] = 'PASS: exact counters asserted by driver'
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: all requested executable checks', flush=True)
    print('Receipt:', a.output.resolve())

if __name__ == '__main__':
    main()
