"""Create the payload manifest and a portable ZIP, excluding build scratch."""
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent


def main():
    paths = []
    for path in sorted(ROOT.rglob('*')):
        relative = path.relative_to(ROOT)
        if not path.is_file() or path.is_symlink():
            continue
        if any(part in ('tmp', '__pycache__') or part.startswith('.')
               for part in relative.parts):
            continue
        if path.suffix == '.pyc' or relative.as_posix() == 'MANIFEST.json':
            continue
        paths.append(path)
    rows = []
    for path in paths:
        data = path.read_bytes()
        rows.append({'path': path.relative_to(ROOT).as_posix(),
                     'bytes': len(data),
                     'sha256': hashlib.sha256(data).hexdigest()})
    manifest = ROOT / 'MANIFEST.json'
    manifest.write_text(json.dumps({
        'format_version': 1,
        'algorithm': 'SHA-256',
        'scope': 'Every distributed payload except this manifest itself.',
        'files': rows,
    }, indent=2) + '\n')
    archive = ROOT.with_name(ROOT.name + '.zip')
    with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED,
                         compresslevel=9) as destination:
        for path in sorted(paths + [manifest]):
            name = (Path(ROOT.name) / path.relative_to(ROOT)).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 10, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            destination.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(archive) as source:
        bad = source.testzip()
        if bad is not None:
            raise SystemExit('ZIP CRC failed: ' + bad)
    data = archive.read_bytes()
    print(json.dumps({'archive': str(archive), 'payload_files': len(paths),
                      'bytes': len(data),
                      'sha256': hashlib.sha256(data).hexdigest(),
                      'zip_crc': 'PASS'}, indent=2))


if __name__ == '__main__':
    main()
