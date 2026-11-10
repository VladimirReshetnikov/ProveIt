"""Write integrity hashes and build the deliverable ZIP deterministically."""
from pathlib import Path
import hashlib
import zipfile

ROOT = Path(__file__).resolve().parent


def included(path):
    relative = path.relative_to(ROOT)
    return (path.is_file() and not any(part.startswith('.') or part == '__pycache__'
            for part in relative.parts) and path.name != 'MANIFEST.sha256'
            and path.suffix not in ('.pyc', '.zip'))


def main():
    files = sorted(p for p in ROOT.rglob('*') if included(p))
    (ROOT / 'MANIFEST.sha256').write_text(''.join(
        hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(ROOT).as_posix() + '\n'
        for p in files))
    files.append(ROOT / 'MANIFEST.sha256')
    destination = ROOT.parent / (ROOT.name + '.zip')
    with zipfile.ZipFile(destination, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(files):
            info = zipfile.ZipInfo((Path(ROOT.name) / path.relative_to(ROOT)).as_posix(),
                                   date_time=(2026, 11, 10, 12, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes())
    print(str(destination))
    print('SHA256 ' + hashlib.sha256(destination.read_bytes()).hexdigest())
    print('Bytes ' + str(destination.stat().st_size))


if __name__ == '__main__':
    main()
