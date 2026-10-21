#!/usr/bin/env python3
"""Check the release manifest and deterministically ZIP its exact listed files."""
from pathlib import Path
import argparse, hashlib, json, zipfile

ROOT = Path(__file__).resolve().parent.parent

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    manifest_path = ROOT / 'manifest.json'
    files = json.loads(manifest_path.read_text())['files']
    entries = {}
    for name, digest in files.items():
        p = ROOT / name
        if not p.resolve().is_relative_to(ROOT) or p.is_symlink():
            raise ValueError('Invalid release path: ' + name)
        raw = p.read_bytes()
        if hashlib.sha256(raw).hexdigest() != digest:
            raise ValueError('Manifest mismatch: ' + name)
        entries[name] = raw
    entries['manifest.json'] = manifest_path.read_bytes()
    out = a.output.resolve()
    if out.exists():
        raise ValueError('Output already exists: ' + str(out))
    out.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(out, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9, strict_timestamps=True) as z:
        for name, raw in sorted(entries.items()):
            info = zipfile.ZipInfo(ROOT.name + '/' + name, (2026, 10, 20, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info, raw, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    print(json.dumps({'path': str(out), 'files': len(entries),
                      'bytes': out.stat().st_size,
                      'sha256': hashlib.sha256(out.read_bytes()).hexdigest()}, indent=2))

if __name__ == '__main__':
    main()
