#!/usr/bin/env python3
"""Write the exact payload manifest and a deterministic ZIP of this packet.

Run from the extracted packet with --zip pointing outside it. This updates
manifest.json after intentional source/report changes. It does not verify
the mathematical claims and must not replace a reproduction run.
"""
import argparse, hashlib, json, stat, zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

def payload():
    files = []
    for path in ROOT.rglob('*'):
        relative = path.relative_to(ROOT)
        if '__pycache__' in relative.parts or '.report-build' in relative.parts:
            continue
        if path.is_symlink():
            raise ValueError('Symlinks are not release payloads: ' + str(path))
        if path.is_file() and path != ROOT/'manifest.json':
            files.append(path)
    return sorted(files, key=lambda p: p.relative_to(ROOT).as_posix())

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--zip', type=Path)
    a = ap.parse_args()
    if a.zip:
        dest = a.zip.resolve()
        if dest == ROOT or ROOT in dest.parents:
            raise ValueError('ZIP must be outside the packet directory')
    files = payload()
    records = [dict(path=p.relative_to(ROOT).as_posix(), size=p.stat().st_size,
                    sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in files]
    manifest = dict(schema_version=1, title='Research toward a 218-state ZFC machine',
                    date='2026-10-20', requested_218_state_goal='UNMET', files=records)
    (ROOT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    if a.zip:
        dest.parent.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(dest, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
            for path in sorted(files+[ROOT/'manifest.json'], key=lambda p: p.relative_to(ROOT).as_posix()):
                info = zipfile.ZipInfo(ROOT.name+'/'+path.relative_to(ROOT).as_posix(), (2026, 10, 20, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                z.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
        print(json.dumps(dict(path=str(dest), bytes=dest.stat().st_size,
                              sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),
                              payload_files=len(records)), indent=2))
    else:
        print('Manifest written for', len(records), 'payload files')

if __name__ == '__main__':
    main()
