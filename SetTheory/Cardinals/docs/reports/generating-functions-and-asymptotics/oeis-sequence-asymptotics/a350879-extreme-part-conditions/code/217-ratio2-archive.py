#!/usr/bin/env python3
"""Verify public payload pins and create a deterministic fresh ZIP archive."""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True, help='new output ZIP outside the source directory')
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    output = args.out.resolve()
    if output == source or source in output.parents or output.exists():
        parser.error('output must be a new file outside the source directory')
    manifest = json.loads((source/'MANIFEST.json').read_text(encoding='utf-8'))
    for name, digest in manifest['sha256'].items():
        p = Path(name)
        if p.is_absolute() or '..' in p.parts:
            raise ValueError('unsafe manifest path')
        file = source/p
        if not file.is_file() or file.is_symlink():
            raise ValueError('missing or symbolic-link payload: '+name)
        if hashlib.sha256(file.read_bytes()).hexdigest() != digest:
            raise ValueError('payload hash mismatch: '+name)
    with zipfile.ZipFile(output, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name in sorted(list(manifest['sha256'])+['MANIFEST.json']):
            info = zipfile.ZipInfo('Report217/'+name, date_time=(2026,10,4,0,0,0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, (source/name).read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    print(hashlib.sha256(output.read_bytes()).hexdigest()+'  '+str(args.out))


if __name__ == '__main__':
    main()
