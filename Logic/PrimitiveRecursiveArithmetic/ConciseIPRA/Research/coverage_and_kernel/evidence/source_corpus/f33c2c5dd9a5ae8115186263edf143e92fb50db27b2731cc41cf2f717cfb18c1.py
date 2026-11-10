"""Build a deterministic ZIP and record the bytes of each distributed member."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / 'MANIFEST.sha256.json'
TARGET = ROOT.parent / 'ipra_named_specialization_2026-11-10.zip'


def members():
    for path in sorted(ROOT.rglob('*')):
        relative = path.relative_to(ROOT)
        if any(part.startswith('.') or part == '__pycache__' for part in relative.parts):
            continue
        if not path.is_file() or path == MANIFEST or path.suffix == '.pyc':
            continue
        yield path


def main():
    files = list(members())
    rows = []
    for path in files:
        data = path.read_bytes()
        rows.append({'path': path.relative_to(ROOT).as_posix(),
                     'bytes': len(data),
                     'sha256': hashlib.sha256(data).hexdigest()})
    MANIFEST.write_text(json.dumps({'version': 1, 'algorithm': 'sha256',
                                    'files': rows}, indent=2) + '\n')
    with zipfile.ZipFile(TARGET, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in sorted(files + [MANIFEST]):
            name = ROOT.name + '/' + path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 10, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    data = TARGET.read_bytes()
    print(json.dumps({'archive': str(TARGET), 'members': len(files) + 1,
                      'bytes': len(data),
                      'sha256': hashlib.sha256(data).hexdigest()}, indent=2))


if __name__ == '__main__':
    main()
