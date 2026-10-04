#!/usr/bin/env python3
"""Select compact review evidence and index, but never modify, external fixtures."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat

O = Path('/workspace/shared/report69-independent-release-tool-review-20261004')
C = Path('/workspace/shared/report69-tool-review-candidate-v5')
D = O / 'dossier'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def write(path, value):
    with path.open('x') as f:
        json.dump(value, f, sort_keys=True, indent=2)
        f.write('\n')

def main():
    assert not D.exists()
    # A complete snapshot of retained external review evidence, before dossier creation.
    external = {}
    ignored = {'EXTERNAL_EVIDENCE_INDEX.json', 'DOSSIER_RECEIPT.json', 'package-dossier.stdout'}
    for p in sorted(O.rglob('*')):
        rel = p.relative_to(O).as_posix()
        if rel in ignored:
            continue
        s = p.lstat()
        row = {'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}
        if stat.S_ISREG(s.st_mode):
            data = p.read_bytes()
            row.update(kind='file', bytes=len(data), sha256=sha(data))
        elif stat.S_ISDIR(s.st_mode):
            row['kind'] = 'directory'
        elif stat.S_ISLNK(s.st_mode):
            row.update(kind='symlink', target=os.readlink(p))
        else:
            row.update(kind='special', file_type=stat.S_IFMT(s.st_mode))
        external[rel] = row
    write(O / 'EXTERNAL_EVIDENCE_INDEX.json', {'format': 'Report69 independent external review evidence index v1',
        'root': str(O), 'scope': 'External snapshot before compact dossier creation; excludes this index, the later dossier and packaging output', 'entries': external})
    D.mkdir(mode=0o700)
    selected = []
    json_names = {'BUILD_RECEIPT.json', 'BUILD_FAILURE.json', 'BUILD_DEPENDENCIES.json', 'PAGE_INVENTORY.json',
                  'PREFLIGHT.json', 'PRESERVATION_BEFORE.json', 'PRESERVATION_AFTER.json',
                  'PRESERVATION_AFTER_FAILURE.json', 'RECORDER_INPUT_UNION.json', 'SELFTEST_RECEIPT.json'}
    prohibited_components = {'science', 'audits', 'qa', 'tools', 'manuscript', 'fixture', 'extracted',
        'synthetic', 'preflight-fixture', 'full-candidate-sealed', 'relocated-complete-candidate',
        'frozen-pin-map-fixture', 'sealed-metadata-fixture'}
    for p in sorted(O.rglob('*')):
        if D == p or D in p.parents or not stat.S_ISREG(p.lstat().st_mode):
            continue
        relative = p.relative_to(O)
        if len(relative.parts) == 1:
            include = p.suffix in {'.py', '.json', '.md', '.stdout'} and p.name not in {'package-dossier.stdout', 'DOSSIER_RECEIPT.json'}
        else:
            exclude = any(part in prohibited_components or part.startswith('fixture-') for part in relative.parts[:-1])
            include = not exclude and (p.suffix in {'.stdout', '.fls', '.log'} or p.name in json_names)
        if include:
            target = D / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(p, target)
            assert p.read_bytes() == target.read_bytes()
            selected.append(relative.as_posix())
    inspected = D / 'inspected-candidate'
    for name in ('README.md', 'tools/release69.py', 'tools/build_report69.py', 'tools/selftest69.py'):
        target = inspected / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(C / name, target)
        selected.append(target.relative_to(D).as_posix())
    rows = {}
    for rel in sorted(selected):
        p = D / rel
        data = p.read_bytes()
        rows[rel] = {'bytes': len(data), 'sha256': sha(data)}
    manifest = {'format': 'Report69 independent compact dossier manifest v1', 'files': rows,
                'external_fixture_policy': 'Bulky fixture copies, duplicate archives, PDF and PNG payloads remain external and are hash-indexed; this manifest lists only actually included files'}
    write(D / 'DOSSIER_MANIFEST.json', manifest)
    receipt = {'status': 'PASS', 'dossier': str(D), 'dossier_files_including_manifest': len(rows) + 1,
               'payload_bytes_excluding_manifest': sum(r['bytes'] for r in rows.values()),
               'review_sha256': rows['REVIEW.md']['sha256'],
               'dossier_manifest_sha256': sha((D / 'DOSSIER_MANIFEST.json').read_bytes()),
               'external_evidence_index_sha256': rows['EXTERNAL_EVIDENCE_INDEX.json']['sha256'],
               'external_entries': len(external)}
    write(O / 'DOSSIER_RECEIPT.json', receipt)
    print(json.dumps(receipt, sort_keys=True, indent=2))

if __name__ == '__main__':
    main()
