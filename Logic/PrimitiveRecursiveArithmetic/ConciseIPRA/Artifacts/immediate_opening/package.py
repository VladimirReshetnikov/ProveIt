"""Build a deterministic ZIP and verify every archived member against its manifest."""
from pathlib import Path
import hashlib
import zipfile

ROOT = Path(__file__).resolve().parent
EXCLUDED_SUFFIXES = {'.aux', '.out', '.toc', '.pyc', '.zip'}


def included(path):
    relative = path.relative_to(ROOT)
    return (path.is_file() and '__pycache__' not in relative.parts
            and path.suffix not in EXCLUDED_SUFFIXES
            and path.name not in {'MANIFEST.sha256', 'report.log'}
            and not path.name.startswith('build_pass_'))


def main():
    pdf = ROOT / 'report.pdf'
    if not pdf.is_file() or not pdf.read_bytes().startswith(b'%PDF-'):
        raise SystemExit('Build the PDF before packaging.')
    files = sorted(path for path in ROOT.rglob('*') if included(path))
    manifest = ROOT / 'MANIFEST.sha256'
    manifest.write_text(''.join(
        hashlib.sha256(path.read_bytes()).hexdigest() + '  '
        + path.relative_to(ROOT).as_posix() + '\n' for path in files
    ), encoding='utf-8')
    archive = ROOT.parent / (ROOT.name + '.zip')
    with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as output:
        for path in files + [manifest]:
            name = ROOT.name + '/' + path.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 12, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            output.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED,
                            compresslevel=9)
    with zipfile.ZipFile(archive) as source:
        if source.testzip() is not None:
            raise SystemExit('ZIP CRC validation failed.')
        for path in files:
            name = ROOT.name + '/' + path.relative_to(ROOT).as_posix()
            if source.read(name) != path.read_bytes():
                raise SystemExit('Archived member differs: ' + name)
    print(archive)
    print('Members:', len(files) + 1)
    print('Bytes:', archive.stat().st_size)
    print('SHA256:', hashlib.sha256(archive.read_bytes()).hexdigest())


if __name__ == '__main__':
    main()
