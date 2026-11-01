#!/usr/bin/env python3
"""Bounded header-reader sample on two audited Foundation modules."""
import json
import os
from pathlib import Path

import closure

HERE = Path(__file__).resolve().parent
ROOT = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun')
RECEIPT = ROOT / 'build-all-receipt.json'
AUDIT = HERE.parent / 'foundation-provider-independent-audit/receipt.json'
INPUT = HERE.parent / 'foundation-provider-recovery/input-manifest.json'
PINS = {
    RECEIPT: '7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6',
    AUDIT: '60b8bcf556c275a33cbd133f1729fef439a2eaf4c3377d53e4ddbcafb9632a9e',
    INPUT: '491075df9eac57799d21b475527b3b1af3dc81ded58e97a87e1cf6c453dcb13d',
}
MODULES = {
    'Foundation.Vorspiel.IsEmpty': 'Mathlib.Logic.IsEmpty.Basic',
    'Foundation.FirstOrder.Arithmetic.IOpen.Basic': 'Foundation.FirstOrder.Arithmetic.Schemata',
}

def main():
    assert all(closure.digest(p) == h for p, h in PINS.items())
    provider = json.loads(RECEIPT.read_text()); manifest = json.loads(INPUT.read_text())
    source = ROOT / 'lib/FormalizedFormalLogic-Foundation'
    paths, guard, sources = [], {}, {}
    for name in MODULES:
        relative = Path(*name.split('.'))
        olean = ROOT / '.lake/build/lib/lean' / relative.with_suffix('.olean')
        ir = olean.with_suffix('.ir')
        assert provider['objects'][name] == closure.digest(olean)
        assert ir.is_file()
        paths.extend([olean, ir]); guard.update(closure.scan(olean))
        src = source / relative.with_suffix('.lean')
        key = str(src.relative_to(source)); assert closure.digest(src) == manifest['foundation_archive_files_sha256'][key]
        assert f'public import {MODULES[name]}' in src.read_text()
        sources[name] = closure.digest(src)
    tool_hashes = {'reader': closure.digest(HERE / 'read_imports.lean'),
                   'driver': closure.digest(HERE / 'closure.py'),
                   'sample': closure.digest(Path(__file__)), 'lean': closure.digest(closure.LEAN)}
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
        env.pop(key, None)
    closure.check_guard(guard)
    rows = closure.read_batch(paths, env)
    closure.check_guard(guard)
    assert all(closure.digest(p) == h for p, h in PINS.items())
    for index, (name, required) in enumerate(MODULES.items()):
        assert all(required in row['imports'] for row in rows[2 * index:2 * index + 2]), name
    out = {'status': 'PASS_FOUR_HEADER_SAMPLE', 'provider_receipt_sha256': PINS[RECEIPT],
           'provider_audit_sha256': PINS[AUDIT], 'input_manifest_sha256': PINS[INPUT],
           'tool_sha256': tool_hashes, 'sources': sources,
           'headers': [{'path': str(path), **row} for path, row in zip(paths, rows)],
           'artifact_guard': guard,
           'scope': 'Two olean and two IR headers from the audited Foundation provider; '
                    'not a full compiled-object closure or runtime provenance audit.'}
    target = HERE / 'provider-sample-receipt.json'
    with target.open('x') as stream:
        json.dump(out, stream, indent=2, sort_keys=True); stream.write('\n')
    print(out['status'], len(paths), closure.digest(target), flush=True)

if __name__ == '__main__':
    main()
