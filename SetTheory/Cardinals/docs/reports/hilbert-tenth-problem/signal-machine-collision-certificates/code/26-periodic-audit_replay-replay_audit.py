#!/usr/bin/env python3
"""Fail-closed Report56 arithmetic replay, using only inspected byte-pinned code.

Original science and audit trees are read-only inputs. Every executed checker is
copied into a fresh external run directory. This is not a physical simulator or
a general machine/macro frontend. Independent proof review is not automated.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys

ROOT = Path(__file__).absolute().parents[1]
INVENTORY = Path(__file__).absolute().with_name('immutable-inputs.json')
INVENTORY_SHA256 = '3151e354e57eabf514c7539d6032cf9fa072d76caac2fede642719b8eacad29a'
PROOF_SHA256 = 'df7cefb472a76e6f34ce7fff0b1e8548782a82f4863fac2ecd2d682c69941a77'
SCHEMA = 'report56-immutable-inputs-v1'

class ReplayError(Exception):
    pass

def require(condition, message):
    if not condition:
        raise ReplayError(message)

def walk_error(error):
    raise error

def sha(data):
    return hashlib.sha256(data).hexdigest()

def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode('utf-8')

def strict_object(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, 'Duplicate JSON key: ' + key)
        out[key] = value
    return out

def parse(data):
    def reject(value):
        raise ReplayError('Invalid JSON constant: ' + value)
    return json.loads(data, object_pairs_hook=strict_object, parse_constant=reject)

def checked_path(path, fresh=False):
    require(path.is_absolute() and '..' not in path.parts, 'Use absolute paths without parent traversal')
    require(path != Path(path.anchor), 'Filesystem root cannot be an input or output')
    current = Path(path.anchor)
    for index, part in enumerate(path.parts[1:], 1):
        current /= part
        leaf = index == len(path.parts) - 1
        try:
            mode = current.lstat().st_mode
        except FileNotFoundError:
            require(leaf and fresh, 'Missing path or parent: ' + str(current))
            continue
        require(not stat.S_ISLNK(mode), 'Symlink path component: ' + str(current))
        require(stat.S_ISDIR(mode), 'Not a directory: ' + str(current))
        if leaf and fresh:
            raise ReplayError('Output must be fresh: ' + str(current))
    return path

def below(path, parent):
    return path == parent or parent in path.parents

def read_regular(path):
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode), 'Not a regular file: ' + str(path))
    fd = os.open(path, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0))
    try:
        opened = os.fstat(fd)
        require((opened.st_dev, opened.st_ino) == (before.st_dev, before.st_ino), 'File changed at open')
        with os.fdopen(fd, 'rb', closefd=False) as stream:
            data = stream.read()
        after = os.fstat(fd)
        require((after.st_size, after.st_mtime_ns) == (opened.st_size, opened.st_mtime_ns),
                'File changed while reading: ' + str(path))
    finally:
        os.close(fd)
    return data

def tree(root, expected=None):
    checked_path(root)
    records, contents, metadata = {}, {}, {}
    for base, dirs, files in os.walk(root, followlinks=False, onerror=walk_error):
        base = Path(base)
        for path in [base] + [base / name for name in sorted(files)]:
            info = path.lstat()
            require(stat.S_ISREG(info.st_mode) or stat.S_ISDIR(info.st_mode),
                    'Nonregular or symlink entry: ' + str(path))
            name = '.' if path == root else path.relative_to(root).as_posix()
            row = {'kind': 'file' if stat.S_ISREG(info.st_mode) else 'directory',
                   'mode': stat.S_IMODE(info.st_mode)}
            if row['kind'] == 'file':
                data = read_regular(path)
                contents[name] = data
                row.update(bytes=len(data), sha256=sha(data))
            records[name] = row
            metadata[name] = (info.st_mode, info.st_mtime_ns, info.st_dev, info.st_ino)
        for name in dirs:
            require(stat.S_ISDIR((base / name).lstat().st_mode),
                    'Non-directory or symlink child: ' + str(base / name))
    if expected is not None:
        require(records == expected, 'Exact inventory, bytes, or mode mismatch: ' + str(root))
    return records, contents, metadata

def write_new(path, data, mode=0o600):
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, 'O_NOFOLLOW', 0), mode)
    try:
        with os.fdopen(fd, 'wb', closefd=False) as stream:
            stream.write(data)
            stream.flush()
        os.fchmod(fd, mode)
    finally:
        os.close(fd)

def snapshot(path, records, contents):
    path.mkdir(mode=0o700)
    for name, row in sorted(records.items(), key=lambda item: (len(Path(item[0]).parts), item[0])):
        if name == '.':
            continue
        target = path / name
        if row['kind'] == 'directory':
            target.mkdir(mode=0o700)
        else:
            write_new(target, contents[name], 0o444)
    for base, dirs, files in os.walk(path, topdown=False, onerror=walk_error):
        Path(base).chmod(0o555)
    return tree(path)

def run_python(output, label, script_name, source, arguments, expected_stdout):
    run = output / label
    run.mkdir(mode=0o700)
    script = run / script_name
    write_new(script, source, 0o444)
    env = {'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8', 'TZ': 'UTC',
           'SOURCE_DATE_EPOCH': '1791072000', 'HOME': str(output / 'home')}
    command = [str(Path(sys.executable).resolve()), '-I', '-B', '-S', str(script), *arguments(run)]
    proc = subprocess.run(command, cwd=run, env=env, stdin=subprocess.DEVNULL,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=900, check=False)
    write_new(run / 'stdout.json', proc.stdout)
    write_new(run / 'stderr.txt', proc.stderr)
    require(proc.returncode == 0, 'Checker failed: ' + label + '; see retained stdout/stderr')
    require(proc.stderr == b'', 'Checker produced stderr: ' + label)
    require(proc.stdout == expected_stdout, 'Receipt bytes mismatch: ' + label)
    require(parse(proc.stdout).get('status') == 'PASS', 'Receipt status mismatch: ' + label)
    require(read_regular(script) == source and stat.S_IMODE(script.stat().st_mode) == 0o444,
            'Executed code copy changed: ' + label)
    return run, {'script_sha256': sha(source), 'stdout_sha256': sha(proc.stdout), 'status': 'PASS'}

def main():
    require(sys.flags.isolated == 1 and sys.flags.optimize == 0,
            'Use python3 -I without -O; independent checks rely on assertions')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, default=ROOT / 'science')
    parser.add_argument('--audit', type=Path, default=ROOT / 'independent_audit')
    parser.add_argument('--output', type=Path, required=True, help='NEW absolute external output; parent must exist')
    args = parser.parse_args()
    packet, audit, output = checked_path(args.packet), checked_path(args.audit), checked_path(args.output, True)
    checked_path(ROOT)
    checked_path(INVENTORY.parent)
    require(not below(packet, audit) and not below(audit, packet), 'Science and audit inputs must be disjoint')
    for source in (ROOT, packet, audit):
        require(not below(output, source) and not below(source, output), 'Output must be disjoint from release and inputs')
    inventory_data = read_regular(INVENTORY)
    require(sha(inventory_data) == INVENTORY_SHA256, 'Immutable inventory SHA256 mismatch')
    require(stat.S_IMODE(INVENTORY.stat().st_mode) == 0o644, 'Immutable inventory mode mismatch')
    manifest = parse(inventory_data)
    require(manifest.get('schema') == SCHEMA, 'Immutable inventory schema mismatch')
    original_packet = tree(packet, manifest['science'])
    original_audit = tree(audit, manifest['independent_audit'])
    science_bytes, audit_bytes = original_packet[1], original_audit[1]
    require(sha(science_bytes['PROOF.md']) == PROOF_SHA256, 'Proof pin mismatch')
    require(audit_bytes['reviewed-proof.md'] == science_bytes['PROOF.md'], 'Reviewed proof is not the author proof')
    # No output creation and no execution occurs until the complete preflight passes.
    output.mkdir(mode=0o700)
    (output / 'home').mkdir(mode=0o700)
    receipts = {}
    try:
        packet_snapshot = output / 'packet_snapshot'
        audit_snapshot = output / 'audit_snapshot'
        packet_copy = snapshot(packet_snapshot, original_packet[0], science_bytes)
        audit_copy = snapshot(audit_snapshot, original_audit[0], audit_bytes)
        run, receipts['author_arithmetic'] = run_python(output, 'author_arithmetic', 'check_arithmetic.py',
            science_bytes['check_arithmetic.py'], lambda run: [], science_bytes['arithmetic_receipt.json'])
        require(set(p.name for p in run.iterdir()) == {'check_arithmetic.py', 'stdout.json', 'stderr.txt'},
                'Unexpected author arithmetic output')
        run, receipts['literal_sign_emitter'] = run_python(output, 'literal_sign_emitter', 'emit_sign_certificate.py',
            science_bytes['emit_sign_certificate.py'], lambda run: ['--output-dir', str(run / 'exports')],
            science_bytes['exports/sign_compiler_receipt.json'])
        expected_exports = {'four_signal_quartic.json', 'quadratic_sign_quartic.json', 'sign_compiler_receipt.json'}
        require(set(p.name for p in run.iterdir()) == {'emit_sign_certificate.py', 'stdout.json', 'stderr.txt', 'exports'},
                'Unexpected literal sign emitter output')
        require(set(p.name for p in (run / 'exports').iterdir()) == expected_exports, 'Unexpected emitter file inventory')
        for name in expected_exports:
            require(read_regular(run / 'exports' / name) == science_bytes['exports/' + name], 'Emitted file mismatch: ' + name)
        emitted_source = run
        emitted_before = tree(emitted_source)
        run, receipts['independent_algebra'] = run_python(output, 'independent_algebra', 'check_exact_algebra.py',
            audit_bytes['check_exact_algebra.py'], lambda run: [], audit_bytes['check-results.json'])
        require(set(p.name for p in run.iterdir()) == {'check_exact_algebra.py', 'stdout.json', 'stderr.txt'},
                'Unexpected independent algebra output')
        run, receipts['independent_emitted_quartics'] = run_python(output, 'independent_emitted_quartics',
            'check_exported_quartics.py', audit_bytes['emitted-artifact-audit/check_exported_quartics.py'],
            lambda run: ['--source-dir', str(emitted_source)], audit_bytes['emitted-artifact-audit/receipt.json'])
        require(set(p.name for p in run.iterdir()) == {'check_exported_quartics.py', 'stdout.json', 'stderr.txt'},
                'Unexpected independent emitted-artifact output')
        require(tree(emitted_source) == emitted_before, 'Freshly emitted arithmetic artifacts changed during audit')
        require(tree(packet_snapshot) == packet_copy, 'Readonly science snapshot changed')
        require(tree(audit_snapshot) == audit_copy, 'Readonly audit snapshot changed')
    finally:
        require(tree(packet, manifest['science']) == original_packet, 'Original science bytes, modes, or mtimes changed')
        require(tree(audit, manifest['independent_audit']) == original_audit, 'Original audit bytes, modes, or mtimes changed')
        require(read_regular(INVENTORY) == inventory_data, 'Immutable input inventory changed')
    result = {'schema': 'report56-arithmetic-replay-v1', 'status': 'PASS',
              'immutable_inventory_sha256': INVENTORY_SHA256, 'proof_sha256': PROOF_SHA256,
              'checks': receipts, 'source_files_verified': len(science_bytes), 'audit_files_verified': len(audit_bytes),
              'original_bytes_modes_mtimes_preserved': True, 'readonly_snapshots_preserved': True,
              'executed_only_inspected_pinned_fresh_arithmetic': True, 'optimization_enabled': False,
              'author_arithmetic_and_emitter_executed': True, 'upstream_or_saved_programs_executed': False,
              'physical_simulator_executed': False, 'general_machine_or_macro_frontend': False,
              'scope': 'Exact byte reproduction and finite arithmetic regressions; no automated proof of infinite claims'}
    receipt_data = encoded(result)
    records = tree(output)[0]
    records['replay-receipt.json'] = {'kind': 'file', 'mode': 0o600, 'bytes': len(receipt_data), 'sha256': sha(receipt_data)}
    write_new(output / 'replay-output-manifest.json', encoded({'schema': 'report56-replay-output-v1', 'entries': records,
              'convention': 'Excludes this output manifest; includes the final success receipt.'}))
    # Publish success last. A failed run retains only partial diagnostic outputs.
    write_new(output / 'replay-receipt.json', receipt_data)
    sys.stdout.buffer.write(receipt_data)

if __name__ == '__main__':
    try:
        main()
    except (ReplayError, OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print('REPLAY FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
