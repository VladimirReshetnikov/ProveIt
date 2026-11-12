"""Create the manifest and deterministic research ZIP from this directory."""
import hashlib
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent
FIXED_TIME = (2026, 11, 10, 0, 0, 0)


def included(path):
    relative = path.relative_to(ROOT)
    return (path.is_file() and not path.is_symlink()
            and not any(part.startswith('.') or part == '__pycache__'
                        for part in relative.parts)
            and path.suffix not in {'.pyc', '.pyo', '.aux', '.log', '.out', '.toc'})


def main():
    manifest = ROOT / 'MANIFEST.sha256'
    files = sorted((path for path in ROOT.rglob('*')
                    if included(path) and path != manifest),
                   key=lambda path: path.relative_to(ROOT).as_posix())
    manifest.write_text(''.join(
        hashlib.sha256(path.read_bytes()).hexdigest() + '  '
        + path.relative_to(ROOT).as_posix() + '\n' for path in files))
    files.append(manifest)
    files.sort(key=lambda path: path.relative_to(ROOT).as_posix())
    destination = ROOT.with_suffix('.zip')
    with zipfile.ZipFile(destination, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in files:
            name = ROOT.name + '/' + path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=FIXED_TIME)
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(destination) as archive:
        bad = archive.testzip()
        if bad is not None:
            raise RuntimeError('ZIP CRC failure: ' + bad)
        if len(archive.infolist()) != len(files):
            raise RuntimeError('ZIP inventory mismatch')
    digest = hashlib.sha256(destination.read_bytes()).hexdigest()
    destination.with_suffix('.zip.sha256').write_text(digest + '  ' + destination.name + '\n')
    print('Archive: ' + str(destination))
    print('Files: ' + str(len(files)))
    print('Bytes: ' + str(destination.stat().st_size))
    print('SHA-256: ' + digest)


if __name__ == '__main__':
    main()
