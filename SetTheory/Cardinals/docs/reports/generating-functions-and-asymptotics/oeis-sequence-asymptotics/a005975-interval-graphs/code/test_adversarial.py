#!/usr/bin/env python3
"""Selected negative tests and ZIP roundtrip, always on throwaway frozen copies."""
import sys
sys.dont_write_bytecode = True
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import secrets
import stat
import subprocess
import zipfile
from output_guard import external_output, write_external_bytes, create_external_directory

ROOT = Path(__file__).resolve().parent

class TestFailure(RuntimeError):
    pass

def require(condition, message):
    if not condition:
        raise TestFailure(message)

def snapshot(root):
    """Content, links and mode bits; no reads through symlinks or special files."""
    entries = {}
    for path in sorted(root.rglob('*')):
        mode = path.lstat().st_mode
        name = path.relative_to(root).as_posix()
        value = os.readlink(path) if stat.S_ISLNK(mode) else (
            sha256(path.read_bytes()).hexdigest() if stat.S_ISREG(mode) else '')
        entries[name] = (mode, value)
    entries['.'] = (root.lstat().st_mode, '')
    return entries

def freeze(root):
    for path in root.rglob('*'):
        mode = path.lstat().st_mode
        if stat.S_ISREG(mode):
            path.chmod(0o444)
    for path in sorted(root.rglob('*'), reverse=True):
        if path.is_dir() and not path.is_symlink():
            path.chmod(0o555)
    root.chmod(0o555)

def thaw(root):
    for path in [root, *root.rglob('*')]:
        if path.is_dir() and not path.is_symlink():
            path.chmod(0o755)
        elif path.is_file() and not path.is_symlink():
            path.chmod(0o644)

def invoke(root, script, arguments=(), optimized=False, timeout=300):
    before = snapshot(root)
    command = [sys.executable, '-B'] + (['-O'] if optimized else []) + [str(root / script), *map(str, arguments)]
    env = os.environ.copy()
    env.update(PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0')
    result = subprocess.run(command, cwd=root, env=env, capture_output=True, timeout=timeout)
    require(snapshot(root) == before, 'TESTED_COMMAND_MUTATED_ITS_BUNDLE: ' + script)
    return result

def must_pass(result, label):
    require(result.returncode == 0, label + ': ' + (result.stdout + result.stderr).decode(errors='replace')[-10000:])

def must_fail(result, label, marker=None):
    require(result.returncode != 0, 'UNEXPECTED_ACCEPTANCE: ' + label)
    if marker is not None:
        require(marker.encode() in result.stderr, 'WRONG_REJECTION: ' + label + ': ' + result.stderr.decode(errors='replace'))

def copy_bundle(source, destination, mutation=None):
    shutil.copytree(source, destination, symlinks=True)
    thaw(destination)
    if mutation is not None:
        mutation(destination)
    freeze(destination)
    return destination

def reseal(root):
    from verify import FILES, MANIFEST
    data = ''.join(sha256((root / name).read_bytes()).hexdigest() + '  ' + name + '\n' for name in FILES)
    (root / MANIFEST).write_text(data, encoding='ascii')

def replace(root, name, old, new):
    path = root / name
    data = path.read_bytes()
    require(data.count(old) == 1, 'SEMANTIC_ANCHOR_NOT_UNIQUE: ' + name + ': ' + repr(old))
    path.write_bytes(data.replace(old, new, 1))

def suite(work):
    from verify import MANIFEST, check_inventory
    base = copy_bundle(ROOT, work / 'baseline')
    control = check_inventory(base)
    inventory_cases = []
    def add(name, mutation):
        inventory_cases.append((name, mutation))
    add('missing_file', lambda p: (p / 'report133.tex').unlink())
    add('changed_file', lambda p: (p / 'README.md').write_bytes(b'changed\n'))
    add('extra_file', lambda p: (p / 'extra.txt').write_bytes(b'extra\n'))
    add('empty_directory', lambda p: (p / 'empty').mkdir())
    def nested(p):
        (p / 'nested').mkdir()
        (p / 'nested/payload.txt').write_bytes(b'nested\n')
    add('nested_directory', nested)
    add('missing_manifest', lambda p: (p / MANIFEST).unlink())
    def link_file(p):
        (p / 'README.md').unlink()
        (p / 'README.md').symlink_to(base / 'README.md')
    add('file_symlink', link_file)
    add('dangling_symlink', lambda p: (p / 'dangling').symlink_to(work / 'absent'))
    def link_manifest(p):
        (p / MANIFEST).unlink()
        (p / MANIFEST).symlink_to(base / MANIFEST)
    add('manifest_symlink', link_manifest)
    add('fifo', lambda p: os.mkfifo(p / 'pipe'))
    original_manifest = control[MANIFEST]
    lines = original_manifest.splitlines(keepends=True)
    manifest_cases = {
        'empty_manifest': b'',
        'duplicate_entry': b''.join([lines[0], *lines]),
        'unsorted_entries': b''.join(reversed(lines)),
        'missing_entry': b''.join(lines[1:]),
        'extra_entry': original_manifest + b'0' * 64 + b'  surprise.txt\n',
        'self_entry': original_manifest + b'0' * 64 + b'  MANIFEST.sha256\n',
        'unsafe_parent_entry': b'0' * 64 + b'  ../README.md\n' + b''.join(lines[1:]),
        'absolute_entry': b'0' * 64 + b'  /README.md\n' + b''.join(lines[1:]),
        'windows_separator': b'0' * 64 + b'  nested\\README.md\n' + b''.join(lines[1:]),
        'uppercase_hash': lines[0][:64].upper() + lines[0][64:] + b''.join(lines[1:]),
        'wrong_hash': b'0' * 64 + lines[0][64:] + b''.join(lines[1:]),
        'missing_final_newline': original_manifest[:-1],
        'crlf': original_manifest.replace(b'\n', b'\r\n'),
        'trailing_blank_line': original_manifest + b'\n',
        'non_ascii': original_manifest + b'\xff\n',
    }
    for name, data in manifest_cases.items():
        add(name, lambda p, data=data: (p / MANIFEST).write_bytes(data))
    inventory_results = []
    for number, (name, mutation) in enumerate(inventory_cases):
        candidate = copy_bundle(base, work / ('inventory-' + str(number)), mutation)
        for optimized in (False, True):
            must_fail(invoke(candidate, 'verify.py', ['--inventory-only'], optimized), name)
        inventory_results.append(name)

    # Deliberately corrupt a payload: every bad output must be rejected BEFORE
    # even this inventory failure, checker work, TeX execution, or temp writes.
    guarded = copy_bundle(base, work / 'guarded', lambda p: (p / 'README.md').write_bytes(b'changed\n'))
    external = work / 'outputs'
    external.mkdir()
    (external / 'existing.txt').write_bytes(b'keep\n')
    (external / 'existing-dir').mkdir()
    (external / 'final-link').symlink_to(external / 'existing.txt')
    (external / 'dangling-link').symlink_to(external / 'absent')
    (external / 'ancestor-link').symlink_to(external / 'existing-dir', target_is_directory=True)
    (external / 'bundle-link').symlink_to(guarded, target_is_directory=True)
    output_cases = [
        ('inside_new', guarded / 'new-output', 'OUTPUT_INSIDE_BUNDLE'),
        ('inside_existing', guarded / 'README.md', 'OUTPUT_INSIDE_BUNDLE'),
        ('existing_file', external / 'existing.txt', 'OUTPUT_ALREADY_EXISTS'),
        ('existing_directory', external / 'existing-dir', 'OUTPUT_ALREADY_EXISTS'),
        ('final_symlink', external / 'final-link', 'OUTPUT_SYMLINK_COMPONENT'),
        ('dangling_final_symlink', external / 'dangling-link', 'OUTPUT_SYMLINK_COMPONENT'),
        ('symlink_ancestor', external / 'ancestor-link/new', 'OUTPUT_SYMLINK_COMPONENT'),
        ('symlink_alias_into_bundle', external / 'bundle-link/new', 'OUTPUT_SYMLINK_COMPONENT'),
        ('missing_parent', external / 'missing/new', 'OUTPUT_PARENT_MISSING'),
        ('regular_file_parent', external / 'existing.txt/new', 'OUTPUT_PARENT_NOT_DIRECTORY'),
        ('dotdot_component', external / 'existing-dir/../new', 'OUTPUT_DOTDOT_COMPONENT'),
    ]
    output_results = []
    for script in ('verify.py', 'check_math.py', 'build.py', 'pack.py', 'test_adversarial.py'):
        for name, destination, marker in output_cases:
            arguments = [destination] if script == 'pack.py' else ['--output', destination]
            external_before = snapshot(external)
            for optimized in (False, True):
                must_fail(invoke(guarded, script, arguments, optimized), script + ':' + name, marker)
            require(snapshot(external) == external_before, 'REJECTED_OUTPUT_CHANGED_EXTERNAL_TREE')
            output_results.append(script + ':' + name)

    # Anchors intentionally identify four independent mathematical checks.
    # Edits are made BEFORE the throwaway copy is frozen, and the copied seal
    # is recomputed, so integrity alone cannot account for the rejection.
    semantic_mutations = [
        ('fishburn_count', b'1014', b'1015'),
        ('serial_graph_count', b'known_serial_graphs = [3, 15, 94]',
         b'known_serial_graphs = [3, 15, 95]'),
        ('diagonal_identity', b"row['T'] - row['R'] == T[n - 1]",
         b"row['T'] - row['R'] == T[n]"),
        ('logarithmic_normalization', b'-2*Q(1,6)**2 == -Q(1,18)',
         b'-2*Q(1,6)**2 == -Q(1,19)'),
    ]
    semantic_results = []
    for number, (name, old, new) in enumerate(semantic_mutations):
        def mutate(p, old=old, new=new):
            replace(p, 'check_math.py', old, new)
            reseal(p)
        candidate = copy_bundle(base, work / ('semantic-' + str(number)), mutate)
        check_inventory(candidate)  # Must pass the refreshed hash seal.
        for optimized in (False, True):
            must_fail(invoke(candidate, 'check_math.py', optimized=optimized), name)
        semantic_results.append(name)

    normal = invoke(base, 'check_math.py')
    optimized = invoke(base, 'check_math.py', optimized=True)
    must_pass(normal, 'normal mathematical control')
    must_pass(optimized, 'optimized mathematical control')
    require(normal.stdout == optimized.stdout, 'CONTROL_NORMAL_OPTIMIZED_BYTES_DIFFER')
    for optimized in (False, True):
        must_fail(invoke(base, 'verify.py', ['--seal'], optimized),
                  'existing seal', 'SEAL_ALREADY_EXISTS')

    first = work / 'first.zip'
    second = work / 'second.zip'
    must_pass(invoke(base, 'pack.py', [first]), 'pack control')
    unpack = work / 'unpacked'
    unpack.mkdir()
    with zipfile.ZipFile(first) as archive:
        infos = archive.infolist()
        expected = ['report133/' + name for name in sorted(control)]
        require([item.filename for item in infos] == expected, 'ZIP_CLOSED_INVENTORY_DIFFER')
        for item in infos:
            require(item.date_time == (2026, 10, 2, 0, 0, 0), 'ZIP_TIMESTAMP_DIFFER')
            require(item.compress_type == zipfile.ZIP_STORED, 'ZIP_COMPRESSION_DIFFER')
            require(item.external_attr >> 16 == 0o100644, 'ZIP_MODE_DIFFER')
            require(not item.extra and not item.comment, 'ZIP_EXTRA_METADATA')
            # The exact closed list above excludes traversal, dirs and duplicates.
        archive.extractall(unpack)
    extracted = unpack / 'report133'
    freeze(extracted)
    require(check_inventory(extracted) == control, 'EXTRACTED_BYTES_DIFFER')
    must_pass(invoke(extracted, 'pack.py', [second]), 'extracted pack control')
    require(first.read_bytes() == second.read_bytes(), 'REPACK_BYTES_DIFFER')
    return {'status': 'PASS', 'modes_for_each_negative': ['normal', 'optimized'],
            'inventory_rejections': inventory_results, 'output_rejections': output_results,
            'resealed_semantic_rejections': semantic_results,
            'negative_invocations': 2 * (len(inventory_results) + len(output_results) + len(semantic_results)) + 2,
            'normal_optimized_math_control_equal': True, 'fresh_extraction_repack_equal': True,
            'tested_bundle_copies_immutable': True, 'delivered_bundle_unchanged': True,
            'zip_sha256': sha256(first.read_bytes()).hexdigest()}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='NEW external JSON file; otherwise stdout only')
    args = parser.parse_args()
    temporary = None
    try:
        if args.output is not None:
            external_output(args.output, ROOT)  # Before reads, checks, copying or temporary writes.
        from verify import check_inventory
        original = snapshot(ROOT)
        check_inventory(ROOT)
        # Ignore TMPDIR: it may point into the delivered bundle. Claim a new
        # explicitly guarded directory under the real POSIX temporary root.
        candidate = Path('/tmp').resolve() / ('report133-adversarial-' + secrets.token_hex(12))
        temporary = create_external_directory(candidate, ROOT)
        result = suite(temporary)
        require(snapshot(ROOT) == original, 'DELIVERED_BUNDLE_CHANGED')
        data = (json.dumps(result, sort_keys=True, indent=2) + '\n').encode()
        if args.output is not None:
            write_external_bytes(args.output, data, ROOT)
        sys.stdout.buffer.write(data)
    except (ValueError, RuntimeError, OSError, subprocess.SubprocessError, zipfile.BadZipFile) as exc:
        print('ADVERSARIAL_FAIL: ' + str(exc), file=sys.stderr)
        return 1
    finally:
        if temporary is not None:
            thaw(temporary)
            shutil.rmtree(temporary)
    return 0

if __name__ == '__main__':
    sys.exit(main())
