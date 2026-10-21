#!/usr/bin/env python3
"""Offline ST215 verification. Python 3 standard library, assertions enabled.

Default: finite reconstruction, exact source/control and blank replay, fixed
logical certificate, saved symbolic metadata and graph comparison. --runtime
also rederives all 6,151 universal whole-tape primitive contracts.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import tempfile
import time

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled; do not use -O.')
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'checks'))


def manifest():
    path = ROOT / 'MANIFEST.json'
    if not path.is_file():
        raise RuntimeError('MANIFEST.json missing')
    data = json.loads(path.read_text())
    for item in data['files']:
        p = ROOT / item['path']
        assert p.is_file(), item['path']
        assert p.stat().st_size == item['bytes'], item['path']
        assert hashlib.sha256(p.read_bytes()).hexdigest() == item['sha256'], item['path']
    return {'status': 'PASS', 'files': len(data['files'])}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--runtime', action='store_true')
    ap.add_argument('--work', type=Path)
    ap.add_argument('--no-manifest', action='store_true',
                    help='For development before the final manifest exists')
    args = ap.parse_args()
    if args.work:
        args.work.mkdir(parents=True, exist_ok=False)
        work = args.work.resolve()
    else:
        work = Path(tempfile.mkdtemp(prefix='st215-replay-'))
    started = time.monotonic()
    result = {'runtime_requested': args.runtime, 'work': str(work)}
    if not args.no_manifest:
        result['manifest'] = manifest()
    import rebuild
    import check_source
    import check_bootstrap
    import check_runtime
    import check_fixed_certificate as fc
    result['reconstruction'] = rebuild.run(ROOT, work)
    result['source'] = check_source.run(ROOT, work)
    result['bootstrap'] = check_bootstrap.run(ROOT, work)
    logical = fc.verify(fc.read_json(ROOT / 'inputs/dominated_rho8_full_certificate.json'), True)[0]
    assert logical['proof_nodes'] == 3728 and logical['term_table_nodes'] == 5160
    (work / 'logical_certificate.json').write_text(json.dumps(logical, indent=2) + '\n')
    result['logical_certificate'] = {'status': 'PASS', 'proof_nodes': 3728,
                                   'scope': 'Dominated-to-unrestricted propositional recovery only'}
    result['runtime_audit'] = check_runtime.audit(ROOT, work)
    import check_comparison
    result['comparison'] = check_comparison.run(ROOT, work)
    if args.runtime:
        result['runtime_fresh'] = check_runtime.run(ROOT, work)
    result['status'] = 'FULL_REPLAY_PASS' if args.runtime else 'FINITE_REPLAY_PASS'
    result['seconds'] = time.monotonic() - started
    result['scope'] = 'Ordinary mathematical verification; not a proof-assistant kernel endpoint.'
    (work / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'work': str(work),
                      'seconds': result['seconds'], 'runtime_requested': args.runtime}, indent=2))


if __name__ == '__main__':
    main()
