#!/usr/bin/env python3
"""Seal the final source/PDF package and make a deterministic ZIP.

Run verify_all.py in normal and optimized modes and build_report.py first.
This command records bytes and checks archive integrity; it is not a proof
or a substitute for the mathematical verifiers.
"""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
NAME = 'con_zfc_calibrated_determinant_guards_2026-10-23.zip'


def deliverable(path):
    return (path.is_file() and '__pycache__' not in path.parts
            and path.suffix not in {'.pyc', '.aux', '.log', '.out', '.toc', '.synctex'}
            and not any(part.startswith('.') for part in path.relative_to(ROOT).parts))


def main():
    if not (ROOT/'report.pdf').is_file():
        raise SystemExit('Build report.pdf before packaging.')
    for mode in ('normal', 'optimized'):
        receipt = json.loads((ROOT/'certificates'/('VERIFICATION_'+mode+'.json')).read_text())
        if receipt['status'] != 'PASS':
            raise SystemExit('Missing passing '+mode+' verification receipt.')
    # Refresh the component's optional convenience manifest after the
    # integrated section has had its paths and line breaks adjusted.
    component = ROOT/'nine_positive'
    component_manifest = {str(p.relative_to(component)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted(component.rglob('*'))
                          if deliverable(p) and p.name != 'MANIFEST.json'}
    (component/'MANIFEST.json').write_text(json.dumps(component_manifest, indent=2)+'\n')
    paths = [p for p in sorted(ROOT.rglob('*')) if deliverable(p) and p.name != 'MANIFEST.sha256']
    lines = [hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(ROOT).as_posix()
             for p in paths]
    (ROOT/'MANIFEST.sha256').write_text('\n'.join(lines)+'\n')
    paths.append(ROOT/'MANIFEST.sha256')
    output = ROOT.parent/NAME
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(paths):
            info = zipfile.ZipInfo(ROOT.name+'/'+path.relative_to(ROOT).as_posix(),
                                   date_time=(2026, 10, 23, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(output) as archive:
        bad = archive.testzip()
        if bad is not None:
            raise ValueError('ZIP integrity failure: '+bad)
        for line in lines:
            digest, relative = line.split('  ', 1)
            raw = archive.read(ROOT.name+'/'+relative)
            if hashlib.sha256(raw).hexdigest() != digest:
                raise ValueError('Archived digest mismatch: '+relative)
    print(json.dumps({'archive': str(output), 'files': len(paths),
                      'bytes': output.stat().st_size,
                      'sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
                      'manifest_and_zip_integrity': 'PASS'}, indent=2))


if __name__ == '__main__':
    main()
