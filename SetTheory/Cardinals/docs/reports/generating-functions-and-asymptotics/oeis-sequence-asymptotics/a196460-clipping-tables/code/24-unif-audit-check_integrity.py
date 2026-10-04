#!/usr/bin/env python3
"""New read-only authentication of frozen input packets; never executes inputs."""
import hashlib
import json
from pathlib import Path
import stat
import sys
import zipfile
from datetime import datetime, timezone

ROOT = Path('/workspace/shared')
HERE = Path(__file__).resolve().parent
NAMES = [
    'growing-sector-truncations-20261004',
    'arity-table-asymptotics-20261004',
    'independent-arity-asymptotics-audit-20261004',
    'two-witness-tensor-compiler-20261004',
    'independent-low-arity-audit-20261004',
]
MANIFEST_PINS = [
    'bf48296dc1bd86689df3dbef9cb3bba99903ec84a32f226e2289ec79ea0a3a29',
    '6ae30398c52b6fe1d07a91346791ed3355e7104c55b19a4103de257299293de1',
    '737af333985bc079ecdd688f1854f7221bb86169db7841d91a1115d2f94e7055',
    'b243e39e0fd9698f9d610f0f6d2b17485a98df8e20a9412c1c38c65877a42c82',
    '6852625bc450563eeda5ad96956e3ac18da64b95ca446c654da14f3b978594b3',
]
ZIP_PINS = [
    '5155553958eb14f2a2bb0c28aa1262cc2e2ad1871aac3b37d6d3efc2c7355c42',
    '11d45c3cf884e722b72d1032e8879f75070a69ec844efe89a919858b8200d345',
    '50247fd9cac35e73e19eb6ce6e9b3318c663c2ea0baec876ecd90a0fcc3d63b0',
    '897a7bee8ab8f0758b8c3b035b7be0d06d9521a9769919266ab30057a6702c8c',
    '3f8811f2217d292ca3d895712e8e7d17465ac51e328ed94eeee80fbc22cfe1a7',
]
EXTRA = [
    'two-witness-tensor-compiler-final-receipt.json',
    'oeis-arity-asymptotics-release-20261004',
    'A196460-clipping-tables-source-evidence-20261004.zip',
    'A196460-clipping-tables-source-evidence-repeat-20261004.zip',
    'A196460-clipping-tables-RELEASE_MANIFEST-20261004.json',
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory():
    roots = [ROOT / name for name in NAMES]
    roots += [ROOT / (name + '.zip') for name in NAMES]
    roots += [ROOT / (name + '-receipt.json') for name in NAMES
              if name != 'two-witness-tensor-compiler-20261004']
    roots += [ROOT / name for name in EXTRA]
    paths = set()
    for base in roots:
        assert base.exists(), str(base)
        paths.add(base)
        if base.is_dir():
            paths.update(base.rglob('*'))
    rows = []
    for p in sorted(paths):
        s = p.lstat()
        assert not p.is_symlink(), str(p)
        assert stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode), str(p)
        row = dict(path=str(p), kind='file' if p.is_file() else 'directory',
                   size=s.st_size, mode=stat.S_IMODE(s.st_mode), mtime_ns=s.st_mtime_ns)
        if p.is_file():
            row['sha256'] = digest(p)
        rows.append(row)
    return rows


def authenticate(name, manifest_pin, zip_pin):
    base = ROOT / name
    manifest = base / 'MANIFEST.sha256'
    assert digest(manifest) == manifest_pin, name
    entries = {}
    for line in manifest.read_text().splitlines():
        wanted, relative = line.split('  ', 1)
        rel = Path(relative)
        assert not rel.is_absolute() and '..' not in rel.parts
        assert len(wanted) == 64 and all(c in '0123456789abcdef' for c in wanted)
        assert relative not in entries
        assert digest(base / rel) == wanted, relative
        entries[relative] = wanted
    expected = set(entries) | {'MANIFEST.sha256'}
    actual = {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}
    assert actual == expected, (name, actual ^ expected)
    archive = ROOT / (name + '.zip')
    assert digest(archive) == zip_pin, name
    with zipfile.ZipFile(archive) as z:
        names = z.namelist()
        assert len(names) == len(set(names)) == len(expected)
        assert set(names) == {name + '/' + r for r in expected}
        for r in sorted(expected):
            info = z.getinfo(name + '/' + r)
            p = base / r
            assert z.read(info) == p.read_bytes(), r
            assert stat.S_IMODE(info.external_attr >> 16) == stat.S_IMODE(p.stat().st_mode)
    return dict(packet=name, manifest_sha256=manifest_pin, archive_sha256=zip_pin,
                payloads=len(entries), zip_members=len(expected), exact_file_set=True,
                archive_bytes_and_modes_equal=True)


def main():
    phase = sys.argv[1]
    assert phase in ('before', 'after')
    rows = inventory()
    result = dict(captured_utc=datetime.now(timezone.utc).isoformat(), objects=rows)
    if phase == 'after':
        before = json.loads((HERE/'evidence/input-before.json').read_text())
        assert rows == before['objects'], 'Frozen input inventory changed'
        result['unchanged_from_before'] = True
    with (HERE/f'evidence/input-{phase}.json').open('x') as f:
        json.dump(result, f, indent=2)
        f.write('\n')
    auth = [authenticate(*args) for args in zip(NAMES, MANIFEST_PINS, ZIP_PINS)]
    target = ROOT / NAMES[0]
    assert digest(target/'PROOF.md') == 'ebd92e3b5bdf684981b2ff248376ac290c57aec403169beee780fef9ea92aa65'
    historical_before = json.loads((target/'evidence/input-before.json').read_text())
    historical_after = json.loads((target/'evidence/input-after.json').read_text())
    assert historical_before['objects'] == historical_after['objects']
    current_by_path = {row['path']:row for row in rows}
    assert all(current_by_path[row['path']] == row for row in historical_after['objects'])
    out = dict(status='PASS', phase=phase, object_count=len(rows),
               authenticated_packets=auth, original_51_object_preservation_matches=True,
               atime_excluded=True, no_source_execution=True)
    with (HERE/f'evidence/integrity-{phase}.json').open('x') as f:
        json.dump(out, f, indent=2)
        f.write('\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
