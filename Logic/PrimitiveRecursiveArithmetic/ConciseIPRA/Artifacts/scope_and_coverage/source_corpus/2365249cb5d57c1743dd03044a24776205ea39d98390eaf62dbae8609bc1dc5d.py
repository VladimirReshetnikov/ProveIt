"""Create the delivery manifest and ZIP from the current local artifacts."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / 'evidence/package_manifest.json'


def included(path):
    relative = path.relative_to(ROOT)
    return (path.is_file() and not path.is_symlink()
            and '.build' not in relative.parts
            and '__pycache__' not in relative.parts
            and path.suffix != '.pyc'
            and path != MANIFEST)


def main():
    files = sorted(path for path in ROOT.rglob('*') if included(path))
    entries = [dict(path=path.relative_to(ROOT).as_posix(),
                    bytes=path.stat().st_size,
                    sha256=hashlib.sha256(path.read_bytes()).hexdigest())
               for path in files]
    MANIFEST.write_text(json.dumps({
        'format': 'SHA-256 file manifest',
        'scope': 'Every delivered file except this manifest itself.',
        'files': entries}, indent=2) + '\n')
    target = ROOT.parent / (ROOT.name + '.zip')
    with zipfile.ZipFile(target, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in sorted(files + [MANIFEST]):
            info = zipfile.ZipInfo(ROOT.name + '/' + path.relative_to(ROOT).as_posix(),
                                   date_time=(2026, 11, 10, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(target) as archive:
        if archive.testzip() is not None:
            raise RuntimeError('ZIP integrity check failed.')
        for item in entries:
            data = archive.read(ROOT.name + '/' + item['path'])
            if hashlib.sha256(data).hexdigest() != item['sha256']:
                raise RuntimeError('Manifest mismatch: ' + item['path'])
    print(json.dumps({'archive': str(target), 'files': len(files) + 1,
                      'bytes': target.stat().st_size,
                      'sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                      'zip_integrity': 'PASS', 'manifest_verification': 'PASS'}, indent=2))


if __name__ == '__main__':
    main()
