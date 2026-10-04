#!/usr/bin/env python3
"""Authenticate relocated immutable inputs, replay only the pinned audit checker.

This is a release adapter, not a signal-machine program or a sandbox. The
reviewer checker is copied byte-for-byte into a new external directory. Source
proofs, the author checker and prior compiler proof are always inert bytes.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys


PINS_SHA256 = '2833e4e52431a495f3923ab6852484c749c550b7e4bab89949ff8a5c1b4d515f'
CHECKER = 'independent_affine_checks.py'
EVIDENCE = 'independent_affine_evidence.json'
CHECKER_SHA256 = '173eb6d22f7b69dd8a96f444fc422c841e2045b07b3ac9dd74a90d3654e66b92'
EVIDENCE_SHA256 = '3a6d31b564f70ccb5173c8997a9e69f2389ee9fc8867ccbcefb112457a1643cb'


class Rejected(Exception):
    pass


def require(condition, message):
    if not condition:
        raise Rejected(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def metadata(s):
    # atime deliberately excluded because reading may legitimately update it.
    return (s.st_dev, s.st_ino, s.st_mode, s.st_nlink, s.st_size, s.st_mtime_ns)


def checked_path(raw, *, fresh=False):
    """Reject lexical aliases and symbolic links in every existing component."""
    p = Path(raw)
    require(p.is_absolute(), 'path must be absolute: '+raw)
    require(str(p) == raw and '..' not in p.parts and not raw.startswith('//'),
            'path must use canonical spelling without aliases: '+raw)
    parts = p.parts
    current = Path(parts[0])
    for index, component in enumerate(parts[1:],1):
        current /= component
        last = index == len(parts)-1
        try:
            s = current.lstat()
        except FileNotFoundError:
            require(fresh and last, 'missing input or output parent: '+str(current))
            return p
        require(not stat.S_ISLNK(s.st_mode), 'symbolic-link path rejected: '+str(current))
        if not last:
            require(stat.S_ISDIR(s.st_mode), 'non-directory path component: '+str(current))
        if last and fresh:
            raise Rejected('output must be fresh and nonexistent: '+str(p))
    require(not fresh, 'output must be fresh and nonexistent: '+str(p))
    return p


def overlaps(a,b):
    return a == b or a in b.parents or b in a.parents


def read_regular(path):
    """Read a stable ordinary single-link file without following a final link."""
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode), 'not a regular file: '+str(path))
    require(before.st_nlink == 1, 'hard-linked file rejected: '+str(path))
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        opened = os.fstat(fd)
        require(metadata(opened) == metadata(before), 'file changed while opening: '+str(path))
        with os.fdopen(fd, 'rb', closefd=False) as handle:
            data = handle.read()
        require(metadata(os.fstat(fd)) == metadata(before), 'file changed while reading: '+str(path))
    finally:
        os.close(fd)
    require(metadata(path.lstat()) == metadata(before), 'file path changed while reading: '+str(path))
    return data, metadata(before)


def authenticate(root, pin):
    """Authenticate the complete file/directory inventory, retaining all bytes."""
    require(stat.S_ISDIR(root.lstat().st_mode), 'input root is not a directory: '+str(root))
    expected_dirs = set(pin['directories'])
    expected_files = pin['files']
    expected_names = expected_dirs | set(expected_files)
    seen, snapshot, contents = set(), {}, {}

    def visit(relative):
        path = root if relative == '.' else root / relative
        s = path.lstat()
        require(not stat.S_ISLNK(s.st_mode), 'symbolic-link input rejected: '+str(path))
        seen.add(relative)
        if stat.S_ISDIR(s.st_mode):
            require(relative in expected_dirs, 'unexpected directory: '+str(path))
            snapshot[relative] = metadata(s)
            with os.scandir(path) as entries:
                names = sorted(entry.name for entry in entries)
            for name in names:
                child = name if relative == '.' else relative+'/'+name
                require(child in expected_names, 'unexpected inventory entry: '+str(root/child))
                visit(child)
        else:
            require(relative in expected_files, 'unexpected file: '+str(path))
            data, snap = read_regular(path)
            expected = expected_files[relative]
            require(len(data) == expected['size'] and digest(data) == expected['sha256'],
                    'input content/hash mismatch: '+str(path))
            contents[relative], snapshot[relative] = data, snap

    visit('.')
    require(seen == expected_names,
            'missing inventory entries: '+repr(sorted(expected_names-seen)))
    return snapshot, contents


def exclusive_write(path, data, mode=0o600):
    fd = os.open(path, os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW, mode)
    with os.fdopen(fd,'wb') as handle:
        handle.write(data)


def run(args):
    require(hasattr(os,'O_NOFOLLOW'), 'this adapter requires POSIX O_NOFOLLOW')
    science = checked_path(args.science_root)
    audit = checked_path(args.audit_root)
    pins_path = checked_path(args.pins)
    output = checked_path(args.output_root, fresh=True)
    adapter = checked_path(os.path.abspath(__file__))
    protected = [('science',science),('audit',audit),('adapter directory',adapter.parent)]
    require(not overlaps(science,audit), 'science and audit roots overlap or alias')
    for name,root in protected:
        require(not overlaps(output,root), 'output overlaps protected '+name)
    require(not overlaps(output,pins_path), 'output overlaps the pins file')
    require(not overlaps(science,adapter.parent) and not overlaps(audit,adapter.parent),
            'input root overlaps adapter directory')

    pins_bytes, pins_before = read_regular(pins_path)
    require(digest(pins_bytes) == PINS_SHA256, 'pins authentication failed')
    pins = json.loads(pins_bytes)
    require(pins['format'] == 1 and set(pins['roots']) == {'science','audit'},
            'unsupported pin format')
    science_before, science_data = authenticate(science,pins['roots']['science'])
    audit_before, audit_data = authenticate(audit,pins['roots']['audit'])
    # Pinned roots are disjoint both lexically and by actual directory identity.
    require(science_before['.'][:2] != audit_before['.'][:2], 'input roots alias one directory')
    identities = set()
    protected_directories = {metadata(adapter.parent.lstat())[:2]}
    for snapshot in (science_before,audit_before):
        for relative, entry in snapshot.items():
            identity = entry[:2]
            require(identity not in identities, 'input entries alias one filesystem object: '+relative)
            identities.add(identity)
            if stat.S_ISDIR(entry[2]):
                protected_directories.add(identity)
    for ancestor in output.parents:
        require(metadata(ancestor.lstat())[:2] not in protected_directories,
                'output parent aliases a protected input directory')
    checker, expected_evidence = audit_data[CHECKER], audit_data[EVIDENCE]
    require(digest(checker) == CHECKER_SHA256, 'reviewer checker pin mismatch')
    require(digest(expected_evidence) == EVIDENCE_SHA256, 'reviewer evidence pin mismatch')

    # No inputs are written. The only executed file is this authenticated copy.
    output.mkdir(mode=0o700, exist_ok=False)
    copied_checker = output/CHECKER
    exclusive_write(copied_checker,checker,mode=0o400)
    interpreter = str(Path(sys.executable).resolve(strict=True))
    completed = None
    try:
        completed = subprocess.run(
            [interpreter,'-I','-S','-B',str(copied_checker)],
            cwd=str(output),
            env={'PATH':os.defpath,'LC_ALL':'C','LANG':'C'},
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=30, check=False,
        )
    finally:
        science_after, _ = authenticate(science,pins['roots']['science'])
        audit_after, _ = authenticate(audit,pins['roots']['audit'])
        pins_after_bytes, pins_after = read_regular(pins_path)
        require(science_after == science_before and audit_after == audit_before,
                'input metadata changed during replay')
        require(pins_after_bytes == pins_bytes and pins_after == pins_before,
                'pins file changed during replay')

    require(completed.returncode == 0, 'reviewer checker failed: '+repr(completed.stderr))
    require(completed.stderr == b'', 'reviewer checker produced unexpected stderr')
    expected_stdout = (json.dumps({'passed':True,'evidence':str(output/EVIDENCE)})+'\n').encode()
    require(completed.stdout == expected_stdout, 'reviewer checker stdout did not match exact expected bytes')
    require(set(p.name for p in output.iterdir()) == {CHECKER,EVIDENCE},
            'unexpected checker output inventory')
    copied_bytes,_ = read_regular(copied_checker)
    actual_evidence,_ = read_regular(output/EVIDENCE)
    require(copied_bytes == checker, 'copied checker changed')
    require(actual_evidence == expected_evidence, 'deterministic evidence differs byte-for-byte')
    exclusive_write(output/'execution_stdout.txt',completed.stdout)
    receipt = {
        'passed':True,
        'pins_sha256':PINS_SHA256,
        'science_root':str(science),
        'audit_root':str(audit),
        'output_root':str(output),
        'science_manifest_sha256':digest(science_data['MANIFEST.json']),
        'audit_manifest_sha256':digest(audit_data['MANIFEST.json']),
        'checker_sha256':digest(copied_bytes),
        'evidence_sha256':digest(actual_evidence),
        'deterministic_evidence_byte_equal':True,
        'stdout_exact_for_output_path':True,
        'inputs_inventory_bytes_modes_mtimes_preserved':True,
        'executed':['authenticated byte-identical independent_affine_checks.py copy'],
        'inert':['all science files','all other audit files'],
        'isolation':'isolated Python (-I -S -B), sanitized environment, fresh cwd; not an OS or network sandbox; trusted interpreter/standard library and quiescent filesystem required',
    }
    exclusive_write(output/'replay_receipt.json',(json.dumps(receipt,indent=2,sort_keys=True)+'\n').encode())
    print(json.dumps({'passed':True,'receipt':str(output/'replay_receipt.json')},sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--science-root',required=True)
    parser.add_argument('--audit-root',required=True)
    parser.add_argument('--pins',required=True)
    parser.add_argument('--output-root',required=True)
    args = parser.parse_args()
    try:
        run(args)
    except (Rejected,OSError,ValueError,KeyError,subprocess.TimeoutExpired) as exc:
        print('REJECTED: '+str(exc),file=sys.stderr)
        return 2
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
