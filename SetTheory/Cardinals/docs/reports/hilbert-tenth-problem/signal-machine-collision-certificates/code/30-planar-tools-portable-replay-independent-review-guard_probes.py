#!/usr/bin/env python3
"""Reviewer-owned synthetic probes; no scientific source is executed."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--adapter', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    adapter = Path(args.adapter).resolve(strict=True)
    out = Path(args.output)
    out.mkdir(exist_ok=False)
    raw = adapter.read_bytes()
    ns = {'__name__': '__independent_review__', '__file__': str(adapter), '__package__': None}
    exec(compile(raw, str(adapter), 'exec', dont_inherit=True, optimize=0), ns)
    tests = []

    def expect_reject(name, function, fragment):
        try:
            function()
        except (RuntimeError, PermissionError) as error:
            if fragment not in str(error):
                raise RuntimeError(name + ': wrong rejection: ' + str(error))
            tests.append({'name': name, 'passed': True, 'diagnostic': str(error)})
        else:
            raise RuntimeError(name + ': unexpected acceptance')

    source = out / 'synthetic-input'; source.mkdir()
    sentinel = source / 'sentinel'; sentinel.write_text('unchanged\n')
    safeout = out / 'synthetic-output'; safeout.mkdir()
    outside = out / 'excluded-input'; outside.mkdir()
    old = outside / 'sentinel'; old.write_text('must not read\n')
    baseline = ns['inventory'](source)
    if ns['canonical_path'](str(source), existing=True) != source:
        raise RuntimeError('Canonical root rejected')
    tests.append({'name': 'canonical_root_accepted', 'passed': True})
    expect_reject('relative_root', lambda: ns['canonical_path']('relative', existing=False), 'explicit and absolute')
    expect_reject('dot_alias', lambda: ns['canonical_path'](str(out) + '/./synthetic-input', existing=True), 'canonical')
    alias = out / 'alias'; alias.symlink_to(source, target_is_directory=True)
    expect_reject('symlink_root', lambda: ns['canonical_path'](str(alias), existing=True), 'canonical')
    expect_reject('symlink_ancestor', lambda: ns['canonical_path'](str(alias / 'child'), existing=False), 'canonical')
    expect_reject('file_as_root', lambda: ns['canonical_path'](str(sentinel), existing=True), 'directory')

    linked = out / 'hardlink'; os.link(sentinel, linked)
    expect_reject('hardlinked_inventory', lambda: ns['inventory'](source), 'Hardlinked')
    linked.unlink()
    sl = source / 'symlink'; sl.symlink_to(old)
    expect_reject('symlink_inventory', lambda: ns['inventory'](source), 'Symlink')
    sl.unlink()
    fifo = source / 'fifo'; os.mkfifo(fifo)
    expect_reject('nonregular_inventory', lambda: ns['inventory'](source), 'Nonregular')
    fifo.unlink()
    # Source directory metadata changed in these disposable probes, but content
    # authentication deliberately remains relocation-independent.
    expected = ns['content_inventory'](baseline)
    ns['authenticate'](source, expected)
    sentinel.write_text('tampered\n')
    expect_reject('changed_bytes', lambda: ns['authenticate'](source, expected), 'Authenticated tree mismatch')
    sentinel.write_text('unchanged\n')
    extra = source / 'extra'; extra.write_bytes(b'')
    expect_reject('extra_file', lambda: ns['authenticate'](source, expected), 'Authenticated tree mismatch')
    extra.unlink()
    expect_reject('comparison_difference', lambda: ns['compare_file'](sentinel, old, []), 'Byte-for-byte')

    owned = out / 'synthetic_owned_assertion.py'
    owned.write_bytes(b'assert False, "review assertion enabled"\n')
    digest = hashlib.sha256(owned.read_bytes()).hexdigest()
    try:
        ns['inspected_namespace'](owned, digest)
    except AssertionError as error:
        if str(error) != 'review assertion enabled': raise
        tests.append({'name': 'owned_assertion_retained_under_optimized_wrapper', 'passed': True,
                      'outer_optimization': sys.flags.optimize})
    else:
        raise RuntimeError('Owned assertion was optimized out')
    expect_reject('checker_digest', lambda: ns['inspected_namespace'](owned, '0' * 64), 'Owned checker changed')

    guard = ns['ReadWriteGuard']([source, safeout], [source], safeout)
    sys.addaudithook(guard)
    try:
        if sentinel.read_bytes() != b'unchanged\n': raise RuntimeError('Allowed input read failed')
        (safeout / 'allowed').write_bytes(b'ok\n')
        tests.append({'name': 'explicit_read_and_fresh_output_write_allowed', 'passed': True})
        expect_reject('live_guard_excluded_read', lambda: old.read_bytes(), 'read outside explicit roots')
        expect_reject('live_guard_protected_write', lambda: sentinel.write_bytes(b'forbidden'), 'write to protected input')
        expect_reject('live_guard_external_write', lambda: (outside / 'forbidden').write_bytes(b'forbidden'), 'write outside fresh output')
        expect_reject('live_guard_relative_read', lambda: Path('relative').read_bytes(), 'relative filesystem')
        expect_reject('live_guard_directory_read', lambda: list(outside.iterdir()), 'read outside explicit roots')
        expect_reject('live_guard_process', lambda: subprocess.run(['/bin/true']), 'process/network')
        expect_reject('live_guard_link', lambda: os.link(sentinel, safeout / 'forbidden-link'), 'rename/link')
    finally:
        guard.active = False
    if sentinel.read_bytes() != b'unchanged\n' or (outside / 'forbidden').exists():
        raise RuntimeError('Denied write changed a target')
    result = {'status': 'PASS', 'adapter_sha256': hashlib.sha256(raw).hexdigest(),
              'no_author_scientific_program_executed': True, 'tests': tests, 'test_count': len(tests)}
    (out / 'GUARD_PROBES.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'test_count': len(tests), 'output': str(out)}, indent=2))

if __name__ == '__main__':
    main()
