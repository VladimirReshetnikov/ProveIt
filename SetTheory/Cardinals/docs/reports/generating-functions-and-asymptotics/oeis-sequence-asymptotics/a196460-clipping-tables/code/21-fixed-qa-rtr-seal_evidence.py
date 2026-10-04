#!/usr/bin/env python3
"""Seal only completed presentation-review evidence, excluding test fixtures."""
import hashlib
import json
from pathlib import Path
import shutil
import stat

ROOT = Path(__file__).absolute().parent
TARGET = ROOT / 'sealed-evidence'
if TARGET.exists():
    raise ValueError('Evidence destination must be fresh')
TARGET.mkdir()
mapping = {}
for name in ('REPORT.md', 'REVIEW_RECEIPT.json', 'RECORDER_REVIEW.json', 'CANDIDATE_BEFORE.json',
             'ORIGINAL_AFTER.json', 'reviewer_check.py', 'verify_recorders.py', 'seal_evidence.py'):
    mapping[name] = ROOT / name
for name in ('release.py', 'build_article.py', 'freeze_inputs.py', 'selftest.py', 'BUILD_DEPENDENCIES_LOCK.json'):
    mapping['subject-tools/' + name] = ROOT / 'candidate/tools' / name
for build in ('locked-build', 'relocated-build'):
    for name in ('BUILD_RECEIPT.json', 'BUILD_DEPENDENCIES.json', 'PREFLIGHT.json', 'PAGE_INVENTORY.json',
                 'RECORDER_INPUT_UNION.json', 'PRESERVATION_BEFORE.json', 'PRESERVATION_AFTER.json',
                 'format.fls', 'compile-1.fls', 'compile-2.fls', 'compile-3.fls'):
        mapping[build + '/' + name] = ROOT / build / name
mapping['owned-tests/SELFTEST_RECEIPT.json'] = ROOT / 'owned-selftests/SELFTEST_RECEIPT.json'
for p in sorted(ROOT.glob('*.stdout')):
    mapping['logs/' + p.name] = p
for relative, source in sorted(mapping.items()):
    s = source.lstat()
    if not stat.S_ISREG(s.st_mode) or s.st_nlink != 1:
        raise ValueError('Unsafe evidence source')
    dest = TARGET / relative
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, dest)
    if dest.read_bytes() != source.read_bytes():
        raise ValueError('Copied evidence differs')

def inventory():
    files, directories = {}, {}
    for p in sorted(TARGET.rglob('*')):
        relative = p.relative_to(TARGET).as_posix()
        if relative == 'EVIDENCE_MANIFEST.json':
            continue
        s = p.lstat()
        row = {'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}
        if stat.S_ISREG(s.st_mode) and s.st_nlink == 1:
            data = p.read_bytes()
            row.update(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
            files[relative] = row
        elif stat.S_ISDIR(s.st_mode):
            directories[relative] = row
        else:
            raise ValueError('Unsafe evidence entry')
    return {'format': 'Independent arity article release-review evidence v1',
            'files': files, 'directories': directories}

manifest = inventory()
raw = (json.dumps(manifest, sort_keys=True, indent=2) + '\n').encode()
(TARGET / 'EVIDENCE_MANIFEST.json').write_bytes(raw)
if inventory() != manifest:
    raise ValueError('Evidence changed while sealing')
pin = hashlib.sha256(raw).hexdigest()
(ROOT / 'SEALED_EVIDENCE_SHA256.txt').write_text(pin + '  sealed-evidence/EVIDENCE_MANIFEST.json\n')
print(json.dumps({'status': 'PASS', 'path': str(TARGET), 'manifest_sha256': pin,
                  'payload_files': len(manifest['files']),
                  'payload_bytes': sum(r['bytes'] for r in manifest['files'].values())}, indent=2))
