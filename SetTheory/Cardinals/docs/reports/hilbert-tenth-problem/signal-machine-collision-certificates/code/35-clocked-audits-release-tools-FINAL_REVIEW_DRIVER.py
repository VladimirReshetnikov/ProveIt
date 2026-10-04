#!/usr/bin/env python3
"""Independent static/release-only adversarial audit. Never imports research code.

All mutations are confined to a newly created review-owned dossier. The candidate
and pinned origin files are read only. Tested executables are the inspected fresh
report release scripts, the system Python interpreter, TeX/PDF tools through the
builder, and system unzip. Each test invocation has an auditable argv and stdout.
"""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import struct
import subprocess
import sys
import time
import zipfile

D = Path(__file__).resolve().parent / 'delta'
D.mkdir()
SOURCE = Path('/workspace/shared/report65-clocked-native-gaps-release-20261004')
EXPECTED = {
    'tools/build_report65.py': '2e7139e00744d75cd353f096387d868b930bf8c53b9868f9ae903e4ad41d4e0c',
    'tools/release65.py': '1ac3a8066038014bb7cfc674fc00f483442279dd8e77662e475409879e4140ee',
    'tools/BUILD_DEPENDENCIES_LOCK.json': '655822c2dee2f0f4d1a0a8d00208579e4a53d558ce8ca385557e1d88c5e614e2',
    'Report65.pdf': '729213d2a1b3cab8bd00912a0bbdc8a035ebd26c4e4af22da4aab5e5e2b89bf8',
    'Report65.tex': '870025b5d7f633890db20ae3d166deeafcf83657f7fc4746ad221aa933719857',
}
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def enc(obj):
    return (json.dumps(obj, sort_keys=True, indent=2) + '\n').encode()
def fresh_json(p, obj):
    with p.open('xb') as f:
        f.write(enc(obj))
def row(p):
    s = p.lstat()
    r = dict(bytes=s.st_size, mode=stat.S_IMODE(s.st_mode), mtime_ns=s.st_mtime_ns,
             ctime_ns=s.st_ctime_ns, type=stat.S_IFMT(s.st_mode))
    if stat.S_ISREG(s.st_mode):
        r['sha256'] = digest(p)
    return r
def snap(root):
    return {str(p.relative_to(root)): row(p) for p in sorted(root.rglob('*'))}

assert all(digest(SOURCE / p) == h for p, h in EXPECTED.items())
baseline = snap(SOURCE)
pins = json.loads((SOURCE / 'INPUT_PINS.json').read_text())
origins = {r['origin']: row(Path(r['origin'])) for r in pins}
fresh_json(D / 'candidate-before.json', baseline)
fresh_json(D / 'origins-before.json', origins)
fresh_json(D / 'review-scope.json', {'candidate': str(SOURCE), 'frozen_hashes': EXPECTED,
                                   'origin_count': len(origins), 'python': sys.version,
                                   'review_driver_sha256': digest(Path(__file__))})
for name in ('logs', 'cases', 'outputs', 'mutant-archives', 'locks'):
    (D / name).mkdir()
BASE = D / 'owned-release'
shutil.copytree(SOURCE, BASE, copy_function=shutil.copy2)
RELEASE = BASE / 'tools/release65.py'
BUILDER = BASE / 'tools/build_report65.py'
LOCK = BASE / 'tools/BUILD_DEPENDENCIES_LOCK.json'
results = []

def run(name, argv, expect=0, absent=None, env=None, note=None, umask=-1):
    before = time.monotonic()
    r = subprocess.run([str(a) for a in argv], stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, env=env, timeout=300, umask=umask)
    (D / 'logs' / (name + '.txt')).write_bytes(r.stdout)
    ok = (r.returncode == 0 if expect == 0 else r.returncode != 0)
    if absent is not None:
        ok = ok and not absent.exists() and not absent.is_symlink()
    item = {'name': name, 'argv': [str(a) for a in argv], 'exit_code': r.returncode,
            'expected': 'success' if expect == 0 else 'rejection', 'pass': ok,
            'elapsed_seconds': round(time.monotonic() - before, 3)}
    if absent is not None:
        item.update(output_must_remain_absent=str(absent), output_absent=not absent.exists())
    if note:
        item['note'] = note
    results.append(item)
    print(name, 'PASS' if ok else 'FAIL', flush=True)
    return r
def release(name, verb, root=BASE, pin=None, extra=(), **kw):
    cmd = [sys.executable, "-I", RELEASE, verb, '--root', root]
    if verb != 'seal':
        cmd += ['--manifest-sha256', pin or PIN]
    return run(name, cmd + list(extra), **kw)
def build(name, root=BASE, pin=None, lock=LOCK, lockpin=None, extra=(), **kw):
    out = D / 'outputs' / name
    cmd = [sys.executable, "-I", BUILDER, '--root', root, '--output', out,
           '--manifest-sha256', pin or PIN]
    if lock is not None:
        cmd += ['--dependency-lock', lock, '--dependency-lock-sha256', lockpin or digest(lock)]
    return run(name, cmd + list(extra), **kw), out
def variant(name, sealed=True):
    root = D / 'cases' / name
    shutil.copytree(BASE, root, copy_function=shutil.copy2)
    if not sealed:
        (root / 'MANIFEST.json').unlink()
    return root
def archivecheck(name, path, pin=None, **kw):
    return run(name, [sys.executable, "-I", RELEASE, 'archive-check', '--archive', path,
                      '--manifest-sha256', pin or PIN], **kw)

# Happy path, including read-only verification against all actual pinned origins.
release('seal-owned-copy', 'seal')
PIN = digest(BASE / 'MANIFEST.json')
fresh_json(D / 'owned-manifest-pin.json', {'manifest_sha256': PIN})
release('verify-metadata-origins', 'verify', extra=['--metadata', '--origins'])
release('refuse-reseal', 'seal', expect=1)
sealed_before = snap(BASE)
build('locked-build')
hostile = os.environ.copy()
for key in ('TEXINPUTS', 'TEXMF', 'TEXMFCNF', 'TEXMFHOME', 'TEXMFVAR',
            'TEXMFCONFIG', 'TEXFORMATS', 'TEXFONTMAPS', 'TEXFONTS',
            'TEXMFOUTPUT', 'BIBINPUTS', 'BSTINPUTS', 'HOME', 'TMPDIR'):
    hostile[key] = '/nonexistent-report65-hostile-environment'
hostile.update(PATH='/nonexistent-report65-hostile-bin', LANG='garbage',
               LC_ALL='garbage', SOURCE_DATE_EPOCH='1', FORCE_SOURCE_DATE='0',
               shell_escape='t', openin_any='a', openout_any='a',
               MKTEXPK='1', MKTEXTFM='1', MKTEXMF='1')
build('hostile-environment-build', env=hostile)
for case in ('locked-build', 'hostile-environment-build'):
    out = D / 'outputs' / case
    check = {n: digest(out / n) for n in ('Report65.pdf', 'Report65.tex', 'BUILD_DEPENDENCIES_LOCK.json')}
    expected = {'Report65.pdf': EXPECTED['Report65.pdf'], 'Report65.tex': EXPECTED['Report65.tex'],
                'BUILD_DEPENDENCIES_LOCK.json': EXPECTED['tools/BUILD_DEPENDENCIES_LOCK.json']}
    results.append({'name': case + '-exact-artifact-hashes', 'pass': check == expected,
                    'actual': check, 'expected': expected})

for suffix in ('a', 'b'):
    release('archive-' + suffix, 'archive', extra=['--output', D / ('repeat-' + suffix + '.zip')])
ZA = D / 'repeat-a.zip'
results.append({'name': 'repeat-zip-byte-identity', 'pass': ZA.read_bytes() == (D / 'repeat-b.zip').read_bytes(),
                'sha256': digest(ZA)})
archivecheck('archive-check-original', ZA)
roundtrip = D / 'extracted'
roundtrip.mkdir()
run('unzip-roundtrip', ['/usr/bin/unzip', '-q', ZA, '-d', roundtrip])
EXTRACTED = roundtrip / 'Report65'
release('verify-extracted', 'verify', root=EXTRACTED)
release('metadata-extracted-rejection', 'verify', root=EXTRACTED, extra=['--metadata'], expect=1,
        note='Expected: ZIP carries canonical seconds, not original nanosecond mtime.')
build('extracted-locked-build', root=EXTRACTED)
results.append({'name': 'extracted-build-exact-hashes', 'pass':
    digest(D / 'outputs/extracted-locked-build/Report65.pdf') == EXPECTED['Report65.pdf'] and
    digest(D / 'outputs/extracted-locked-build/Report65.tex') == EXPECTED['Report65.tex']})

# Build preflight failures must not create their proposed output directories.
build('bad-manifest-preflight', pin='0' * 64, expect=1, absent=D / 'outputs/bad-manifest-preflight')
build('bad-lock-digest-preflight', lockpin='0' * 64, expect=1, absent=D / 'outputs/bad-lock-digest-preflight')
build('missing-lock-preflight', lock=None, expect=1, absent=D / 'outputs/missing-lock-preflight')
for name, mutate in (
    ('executable-lock-preflight', lambda l: l['executables']['pdftex'].update(sha256='0' * 64)),
    ('input-lock-preflight', lambda l: next(iter(l['system_inputs'].values())).update(sha256='0' * 64)),
    ('invalid-input-path-preflight', lambda l: l['system_inputs'].update({'/tmp/report65-forbidden-lock': {'sha256': '0' * 64, 'bytes': 0}})),
):
    lock = json.loads(LOCK.read_text())
    mutate(lock)
    path = D / 'locks' / (name + '.json')
    fresh_json(path, lock)
    build(name, lock=path, expect=1, absent=D / 'outputs' / name)
existing = D / 'outputs' / 'existing-build-output'
existing.mkdir()
(existing / 'sentinel').write_text('preserve me\n')
build('existing-build-output', expect=1)
results.append({'name': 'existing-build-output-preserved', 'pass': (existing / 'sentinel').read_text() == 'preserve me\n' and len(list(existing.iterdir())) == 1})
run('draft-refuses-sealed', [sys.executable, "-I", BUILDER, '--root', BASE, '--output', D / 'outputs/draft-sealed', '--draft'], expect=1, absent=D / 'outputs/draft-sealed')
run('build-refuses-overlap', [sys.executable, "-I", BUILDER, '--root', BASE, '--output', BASE / 'forbidden-build', '--manifest-sha256', PIN], expect=1, absent=BASE / 'forbidden-build')
parentlink = D / 'linked-output-parent'
parentlink.symlink_to(D / 'outputs', target_is_directory=True)
run('build-refuses-symlink-parent', [sys.executable, "-I", BUILDER, '--root', BASE, '--output', parentlink / 'forbidden-build', '--manifest-sha256', PIN], expect=1, absent=D / 'outputs/forbidden-build')
rootlink = D / 'linked-root'
rootlink.symlink_to(BASE, target_is_directory=True)
release('verify-refuses-symlink-root', 'verify', root=rootlink, expect=1)

# Filesystem and manifest adversaries, entirely in independent fresh copies.
for name, mutate in (
    ('extra-file', lambda r: (r / 'extra.txt').write_text('extra')),
    ('changed-file', lambda r: (r / 'README.md').write_text('changed')),
    ('changed-mode', lambda r: (r / 'README.md').chmod(0o600)),
    ('missing-file', lambda r: (r / 'README.md').unlink()),
    ('symlink-file', lambda r: (r / 'extra-link').symlink_to('README.md')),
    ('symlink-directory', lambda r: (r / 'extra-link').symlink_to('manuscript', target_is_directory=True)),
    ('fifo-file', lambda r: os.mkfifo(r / 'extra-fifo')),
    ('extra-empty-directory', lambda r: (r / 'unexpected-empty').mkdir()),
    ('changed-manifest', lambda r: (r / 'MANIFEST.json').write_bytes((r / 'MANIFEST.json').read_bytes() + b'\n')),
):
    root = variant(name)
    mutate(root)
    release('verify-rejects-' + name, 'verify', root=root, expect=1)
    release('archive-rejects-' + name, 'archive', root=root, extra=['--output', D / 'outputs' / (name + '.zip')], expect=1, absent=D / 'outputs' / (name + '.zip'))
    if name != 'extra-empty-directory':
        build('build-rejects-' + name, root=root, expect=1, absent=D / 'outputs' / ('build-rejects-' + name))

for name, mutate in (
    ('unsafe-pin-path', lambda x: x[0].update(copy='../README.md')),
    ('duplicate-pin-path', lambda x: x.append(copy.deepcopy(x[0]))),
    ('bad-pinned-hash', lambda x: x[0].update(sha256='0' * 64)),
):
    root = variant(name, sealed=False)
    pinrows = json.loads((root / 'INPUT_PINS.json').read_text())
    mutate(pinrows)
    (root / 'INPUT_PINS.json').write_bytes(enc(pinrows))
    release('seal-rejects-' + name, 'seal', root=root, expect=1, absent=root / 'MANIFEST.json')
root = variant('empty-directory-seal', sealed=False)
(root / 'empty').mkdir()
release('seal-rejects-empty-directory', 'seal', root=root, expect=1, absent=root / 'MANIFEST.json')

# Archive adversaries reconstruct ZIPs without extracting or executing members.
with zipfile.ZipFile(ZA) as z:
    members = [(copy.copy(i), z.read(i)) for i in z.infolist()]
TARGET = 'Report65/README.md'
def mutant(name, transform):
    path = D / 'mutant-archives' / (name + '.zip')
    selected = transform(copy.deepcopy(members))
    with zipfile.ZipFile(path, 'x') as z:
        for info, data in selected:
            z.writestr(info, data)
    return path
def edit_target(items, fn, target=TARGET):
    return [fn(i, b) if i.filename == target else (i, b) for i, b in items]
def alter_info(i, b, **kw):
    for k, v in kw.items():
        setattr(i, k, v)
    return i, b
def extra_member(items, name):
    i = copy.copy(items[0][0])
    i.filename = name
    return items + [(i, b'extra')]
mutants = {
    'duplicate-member': lambda x: x + [copy.deepcopy(x[0])],
    'extra-member': lambda x: extra_member(x, 'Report65/extra.txt'),
    'traversal-member': lambda x: extra_member(x, 'Report65/../escape'),
    'absolute-member': lambda x: extra_member(x, '/escape'),
    'backslash-member': lambda x: extra_member(x, 'Report65/foo\\escape'),
    'dot-component-member': lambda x: extra_member(x, 'Report65/foo/./escape'),
    'empty-component-member': lambda x: extra_member(x, 'Report65/foo//escape'),
    'directory-member': lambda x: extra_member(x, 'Report65/empty/'),
    'missing-member': lambda x: [(i, b) for i, b in x if i.filename != TARGET],
    'changed-content': lambda x: edit_target(x, lambda i, b: (i, b + b'changed')),
    'changed-mode': lambda x: edit_target(x, lambda i, b: alter_info(i, b, external_attr=(stat.S_IFREG | 0o600) << 16)),
    'symlink-member': lambda x: edit_target(x, lambda i, b: alter_info(i, b, external_attr=(stat.S_IFLNK | 0o777) << 16)),
    'fifo-member': lambda x: edit_target(x, lambda i, b: alter_info(i, b, external_attr=(stat.S_IFIFO | 0o644) << 16)),
    'changed-timestamp': lambda x: edit_target(x, lambda i, b: alter_info(i, b, date_time=(2026, 10, 5, 0, 0, 0))),
    'changed-archive-manifest': lambda x: edit_target(x, lambda i, b: (i, b + b'\n'), 'Report65/MANIFEST.json'),
}
for name, fn in mutants.items():
    archivecheck('zip-rejects-' + name, mutant(name, fn), expect=1)

# Flag-byte mutation ensures the archive contains a genuine encrypted-member flag.
encrypted = bytearray(ZA.read_bytes())
for sig, offset in ((b'PK\x03\x04', 6), (b'PK\x01\x02', 8)):
    start = 0
    while True:
        at = encrypted.find(sig, start)
        if at < 0:
            break
        flags = struct.unpack_from('<H', encrypted, at + offset)[0]
        struct.pack_into('<H', encrypted, at + offset, flags | 1)
        start = at + 4
encrypted_path = D / 'mutant-archives/encrypted.zip'
encrypted_path.write_bytes(encrypted)
archivecheck('zip-rejects-encrypted', encrypted_path, expect=1)

# Regressions for all independently demonstrated gaps.
manifest_mode = mutant('manifest-mode', lambda x: edit_target(x,
    lambda i, b: alter_info(i, b, external_attr=(stat.S_IFREG | 0o777) << 16), 'Report65/MANIFEST.json'))
archivecheck('fixed-rejects-manifest-archive-mode', manifest_mode, expect=1)
build('fixed-rejects-extra-directory', root=D / 'cases/extra-empty-directory', expect=1,
      absent=D / 'outputs/fixed-rejects-extra-directory')
root_mode = variant('manifest-root-mode')
(root_mode / 'MANIFEST.json').chmod(0o777)
release('fixed-rejects-manifest-filesystem-mode', 'verify', root=root_mode, expect=1)
build('fixed-build-rejects-manifest-mode', root=root_mode, expect=1,
      absent=D / 'outputs/fixed-build-rejects-manifest-mode')
for artifact in ('Report65.tex', 'Report65.pdf'):
    case = 'inconsistent-' + artifact.split('.')[-1]
    root = variant(case, sealed=False)
    with (root / artifact).open('ab') as f:
        f.write(b'\n% Review-owned inconsistent artifact\n')
    release('seal-' + case, 'seal', root=root)
    pin = digest(root / 'MANIFEST.json')
    name = 'fixed-rejects-' + case
    extra = {'absent': D / 'outputs' / name} if artifact.endswith('.tex') else {}
    build(name, root=root, pin=pin, expect=1, **extra)
    output = D / 'outputs' / name
    results.append({'name': name + '-no-success-artifacts', 'pass':
        not (output / 'BUILD.json').exists() and not (output / 'Report65.pdf').exists(),
        'note': 'PDF mismatch occurs after compilation; diagnostics are retained, but no success receipt or final PDF is promoted.'})
root = variant('restrictive-umask', sealed=False)
release('seal-restrictive-umask', 'seal', root=root, umask=0o077)
results.append({'name': 'seal-enforces-manifest-mode-under-umask',
                'pass': stat.S_IMODE((root / 'MANIFEST.json').stat().st_mode) == 0o644})
release('verify-restrictive-umask-seal', 'verify', root=root, pin=digest(root / 'MANIFEST.json'))
for case in ('locked-build', 'hostile-environment-build', 'extracted-locked-build'):
    receipt = json.loads((D / 'outputs' / case / 'BUILD.json').read_text())
    results.append({'name': case + '-sealed-equality-receipt', 'pass': receipt.get('sealed_artifacts_matched') is True})
# Canonical ZIP metadata regressions: old fixtures retain their own manifest pin.
old = D.parent
old_pin = json.loads((old / 'owned-manifest-pin.json').read_text())['manifest_sha256']
for fixture in ('unicode-path-extra.zip', 'unicode-local-only.zip', 'unicode-central-only.zip'):
    archivecheck('fixed-rejects-' + fixture[:-4], old / fixture, pin=old_pin, expect=1)
for name, fn in (
    ('central-extra', lambda x: edit_target(x, lambda i, b: alter_info(i, b, extra=b'\xfe\xca\x00\x00'))),
    ('member-comment', lambda x: edit_target(x, lambda i, b: alter_info(i, b, comment=b'review metadata'))),
):
    archivecheck('fixed-rejects-' + name, mutant(name, fn), expect=1)
comment_archive = D / 'mutant-archives/archive-comment.zip'
shutil.copy2(ZA, comment_archive)
with zipfile.ZipFile(comment_archive, 'a') as z:
    z.comment = b'review metadata'
archivecheck('fixed-rejects-archive-comment', comment_archive, expect=1)

after = snap(SOURCE)
origins_after = {p: row(Path(p)) for p in origins}
fresh_json(D / 'candidate-after.json', after)
fresh_json(D / 'origins-after.json', origins_after)
# The parent may concurrently add QA files. Exact comparison for all preexisting
# candidate regular files avoids attributing authorized directory additions to us.
changed = {p: {'before': r, 'after': after.get(p)} for p, r in baseline.items()
           if stat.S_ISREG(r['type']) and r != after.get(p)}
results.append({'name': 'candidate-existing-files-preserved', 'pass': not changed, 'changes': changed})
results.append({'name': 'all-pinned-origins-preserved', 'pass': origins == origins_after})
results.append({'name': 'owned-base-preserved-after-seal', 'pass': sealed_before == snap(BASE)})
fresh_json(D / 'RESULTS.json', {'tests': results, 'passed': sum(bool(r['pass']) for r in results),
    'total': len(results), 'frozen_hashes': EXPECTED, 'owned_manifest_sha256': PIN,
    'preservation_note': 'bytes, mode, size, mtime_ns and ctime_ns checked; access time is outside the source pins and may be affected by ordinary reads',
    'prohibited_execution': 'No research/audit mathematical code, simulation, saved schedule, native interpreter or Lean was imported or executed.'})
print('RESULTS', sum(bool(r['pass']) for r in results), '/', len(results), flush=True)
