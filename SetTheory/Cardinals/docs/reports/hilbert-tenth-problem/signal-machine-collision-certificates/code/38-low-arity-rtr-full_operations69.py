#!/usr/bin/env python3
"""Independent whole-candidate sealing and relocated replay orchestration."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import zipfile

C = Path('/workspace/shared/report69-tool-review-candidate-v5')
O = Path('/workspace/shared/report69-independent-release-tool-review-20261004')
MANUSCRIPT = '38b3f7a8a3bb1f837ace42df35edffd8d7627d3af476f4869106903e31824e4c'
LOCK = '62d196ba3a660790910afa4ac4eb83f1410b8b64e6a401ad52d1388ee812f3f5'
RESULTS = []

def sha(data):
    return hashlib.sha256(data).hexdigest()

def run(label, root, tool, *args):
    result = subprocess.run([sys.executable, '-I', '-S', '-B', str(root / 'tools' / tool), *args],
                            cwd=O, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
    (O / (label + '.stdout')).write_bytes(result.stdout)
    assert result.returncode == 0, (label, result.stdout[-4000:])
    RESULTS.append({'test': label, 'status': 'PASS', 'returncode': 0})

def page_inventory(folder):
    return {p.name: {'bytes': len(p.read_bytes()), 'sha256': sha(p.read_bytes())} for p in sorted(folder.iterdir())}

def main():
    fixture = O / 'full-candidate-sealed'
    shutil.copytree(C, fixture, copy_function=shutil.copy2)
    manifest = O / 'full-candidate-manifest.json'
    run('full-candidate-manifest', fixture, 'release69.py', 'manifest', '--output', str(manifest))
    shutil.copy2(manifest, fixture / 'RELEASE_MANIFEST.json')
    pin = sha(manifest.read_bytes())
    run('full-candidate-verify', fixture, 'release69.py', 'verify', '--manifest-sha256', pin)
    archives = [O / ('full-candidate-' + suffix + '.zip') for suffix in ('a', 'b')]
    for suffix, path in zip(('a', 'b'), archives):
        run('full-candidate-archive-' + suffix, fixture, 'release69.py', 'archive', '--manifest-sha256', pin, '--output', str(path))
    assert archives[0].read_bytes() == archives[1].read_bytes()
    RESULTS.append({'test': 'full-candidate-byte-identical-archives', 'status': 'PASS', 'sha256': sha(archives[0].read_bytes())})
    manifest_data = json.loads(manifest.read_bytes())
    with zipfile.ZipFile(archives[0]) as archive:
        assert archive.namelist() == sorted(archive.namelist())
        assert all(i.date_time == (2026, 10, 4, 0, 0, 0) and i.compress_type == zipfile.ZIP_DEFLATED and i.create_system == 3 for i in archive.infolist())
        assert all(stat.S_ISREG(i.external_attr >> 16) for i in archive.infolist())
        assert archive.testzip() is None
        RESULTS.append({'test': 'fixed-zip-container-shape', 'status': 'PASS', 'members': len(archive.namelist())})
    relocated = O / 'relocated-complete-candidate'
    run('full-candidate-extract', fixture, 'release69.py', 'extract', '--manifest-sha256', pin, '--archive', str(archives[0]), '--output-dir', str(relocated))
    run('relocated-complete-verify', relocated, 'release69.py', 'verify', '--manifest-sha256', pin)
    assert stat.S_IMODE(relocated.stat().st_mode) == 0o700
    for kind in ('files', 'directories'):
        for name, row in manifest_data[kind].items():
            path = relocated / name
            s = path.stat()
            assert stat.S_IMODE(s.st_mode) == row['mode'] and s.st_mtime_ns == row['mtime_ns']
            if kind == 'files':
                assert len(path.read_bytes()) == row['bytes'] and sha(path.read_bytes()) == row['sha256']
    RESULTS.append({'test': 'independent-extracted-byte-mode-nanosecond-inventory', 'status': 'PASS'})
    build = O / 'relocated-complete-build'
    run('relocated-complete-build', relocated, 'build_report69.py', '--output-dir', str(build), '--pins-sha', MANUSCRIPT, '--dependency-lock-sha', LOCK, '--require-packaged-match')
    for directory in (O / 'candidate-build', build):
        assert (directory / 'Report69.pdf').read_bytes() == (C / 'Report69.pdf').read_bytes()
        assert (directory / 'BUILD_DEPENDENCIES.json').read_bytes() == (C / 'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes()
        assert (directory / 'PAGE_INVENTORY.json').read_bytes() == (C / 'qa/locked-final-build/PAGE_INVENTORY.json').read_bytes()
        assert page_inventory(directory / 'pages') == page_inventory(C / 'qa/locked-final-build/pages')
        receipt = json.loads((directory / 'BUILD_RECEIPT.json').read_bytes())
        assert receipt['status'] == 'PASS' and receipt['packaged_pdf_match'] and receipt['recorded_passes'] == 4
        union = json.loads((directory / 'RECORDER_INPUT_UNION.json').read_bytes())
        assert len(union['passes']) == 4
        combined = set().union(*(set(p['system_inputs']) for p in union['passes']))
        maps = {p for p in union['union'] if p.endswith(('/lm.map', '/cm.map', '/cmextra.map', '/symbols.map', '/latxfont.map'))}
        assert combined | maps == set(union['union'])
        RESULTS.append({'test': directory.name + '-exact-pdf-and-every-png-and-lock', 'status': 'PASS', 'pages': len(page_inventory(directory / 'pages')), 'system_inputs': len(union['union'])})
    data = {'status': 'PASS', 'scope': 'Presentation-only full candidate operations; no scientific code executed', 'candidate': str(C),
            'manifest_sha256': pin, 'archive_sha256': sha(archives[0].read_bytes()), 'tests': RESULTS}
    (O / 'FULL_OPERATIONS_RECEIPT.json').write_text(json.dumps(data, sort_keys=True, indent=2) + '\n')
    print(json.dumps(data, sort_keys=True, indent=2))

if __name__ == '__main__':
    main()
