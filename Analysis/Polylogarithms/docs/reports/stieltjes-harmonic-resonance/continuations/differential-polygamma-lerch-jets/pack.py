#!/usr/bin/env python3
"""Create a deterministic ZIP and hash manifests for the research package."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent
EXCLUDED_PARTS = {'_build', '__pycache__', '.git'}
EXCLUDED_NAMES = {'package_manifest.json', 'SHA256SUMS'}
ALLOWED_SUFFIXES = {'.tex', '.pdf', '.py', '.json', '.md', '.txt'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    payload = sorted(p for p in ROOT.rglob('*') if p.is_file()
                     and not (set(p.relative_to(ROOT).parts) & EXCLUDED_PARTS)
                     and p.name not in EXCLUDED_NAMES
                     and p.suffix.lower() in ALLOWED_SUFFIXES)
    manifest = {
        'package': ROOT.name, 'source_revision': 'f7e35be357654198c1546fd40f363694c5bcc2cc',
        'files': [{'path': p.relative_to(ROOT).as_posix(),
                   'bytes': p.stat().st_size, 'sha256': digest(p)} for p in payload],
        'excluded': 'Build intermediates, caches, source-retrieval copies, and rendered-review PNGs.',
        'interpretation': 'Hashes attest file identity, not mathematical correctness.'
    }
    manifest_path = ROOT / 'package_manifest.json'
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    payload.append(manifest_path)
    sums = ROOT / 'SHA256SUMS'
    sums.write_text(''.join(f'{digest(p)}  {p.relative_to(ROOT).as_posix()}\n'
                            for p in sorted(payload)))
    payload.append(sums)
    archive = ROOT.parent / (ROOT.name + '.zip')
    with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as output:
        for path in sorted(payload):
            info = zipfile.ZipInfo(ROOT.name + '/' + path.relative_to(ROOT).as_posix(),
                                   date_time=(2026, 10, 11, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            output.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(archive) as check:
        assert check.testzip() is None
        assert len(check.namelist()) == len(payload)
        for path in payload:
            assert check.read(ROOT.name + '/' + path.relative_to(ROOT).as_posix()) == path.read_bytes()
    print(json.dumps({'archive': str(archive), 'files': len(payload),
                      'bytes': archive.stat().st_size, 'sha256': digest(archive)}, indent=2))


if __name__ == '__main__':
    main()
