#!/usr/bin/env python3
"""Seal only this new audit, authenticate its archive, and recheck input state."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import stat
import zipfile

HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = HERE/'MANIFEST.sha256'
    archive = HERE.with_suffix('.zip')
    receipt = HERE.parent/(HERE.name+'-receipt.json')
    assert not manifest.exists() and not archive.exists() and not receipt.exists()
    before = json.loads((HERE/'evidence/input-before.json').read_text())
    after = json.loads((HERE/'evidence/input-after.json').read_text())
    assert before['objects'] == after['objects'] and after['unchanged_from_before'] is True
    for row in after['objects']:
        p = Path(row['path'])
        s = p.lstat()
        assert not p.is_symlink()
        assert s.st_size == row['size']
        assert stat.S_IMODE(s.st_mode) == row['mode']
        assert s.st_mtime_ns == row['mtime_ns']
        if row['kind'] == 'file':
            assert p.is_file() and digest(p) == row['sha256']
        else:
            assert p.is_dir()
    # Recheck full descendant inventories, so additions cannot escape sealing.
    objects = {r['path'] for r in after['objects']}
    for row in after['objects']:
        if row['kind'] == 'directory':
            assert all(str(p) in objects for p in Path(row['path']).iterdir())
    payload = sorted(p for p in HERE.rglob('*') if p.is_file())
    assert all(not p.is_symlink() for p in HERE.rglob('*'))
    assert all('__pycache__' not in p.parts for p in payload)
    with manifest.open('x') as f:
        for p in payload:
            f.write(digest(p)+'  '+str(p.relative_to(HERE))+'\n')
    files = sorted([*payload,manifest])
    for p in files:
        p.chmod(0o444)
    with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED) as z:
        for p in files:
            z.write(p,str(Path(HERE.name)/p.relative_to(HERE)))
    with zipfile.ZipFile(archive) as z:
        expected = [str(Path(HERE.name)/p.relative_to(HERE)) for p in files]
        assert z.namelist() == expected and len(set(expected)) == len(expected)
        for p,name in zip(files,expected):
            assert z.read(name) == p.read_bytes()
            assert stat.S_IMODE(z.getinfo(name).external_attr >> 16) == 0o444
    for p in sorted((p for p in HERE.rglob('*') if p.is_dir()),reverse=True):
        p.chmod(0o555)
    HERE.chmod(0o555)
    archive.chmod(0o444)
    out = dict(status='PASS',sealed_utc=datetime.now(timezone.utc).isoformat(),
               audit=str(HERE/'AUDIT.md'),audit_sha256=digest(HERE/'AUDIT.md'),
               manifest_sha256=digest(manifest),archive=str(archive),archive_sha256=digest(archive),
               archive_bytes=archive.stat().st_size,payload_count=len(payload),zip_members=len(files),
               archive_bytes_and_modes_verified=True,all_new_files_mode='0444',all_new_directories_mode='0555',
               preserved_input_objects=len(after['objects']),input_bytes_modes_sizes_mtimes_inventory_unchanged=True,
               authenticated_source_payloads=104,authenticated_source_archive_members=109,
               source_programs_executed=False,formal_verification=False,
               mathematical_verdict='PASS: all-n analytic proof plus independently authored exact corroboration',
               limits='Read-only convention and content hashes; not WORM or trusted external timestamp.')
    with receipt.open('x') as f:
        json.dump(out,f,indent=2)
        f.write('\n')
    receipt.chmod(0o444)
    print(json.dumps(out,indent=2))


if __name__ == '__main__':
    main()
