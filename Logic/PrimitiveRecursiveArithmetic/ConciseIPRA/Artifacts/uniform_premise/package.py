"""Refresh the artifact manifest and create a deterministic research ZIP."""
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent


def included(path):
    if not path.is_file() or '__pycache__' in path.parts:
        return False
    if path.name == 'MANIFEST.json' or path.suffix in {'.aux', '.out', '.toc', '.pyc'}:
        return False
    return True


def main():
    files = sorted(p for p in ROOT.rglob('*') if included(p))
    manifest = {'title': 'A uniform-premise presentation of iPRA',
                'date': '2026-11-10',
                'comparison_commit': '76a2651601d17b34d46753f189ea026a21ce8d29',
                'files': [{'path': p.relative_to(ROOT).as_posix(),
                           'bytes': p.stat().st_size,
                           'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]}
    (ROOT / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    destination = ROOT.parent / (ROOT.name + '.zip')
    with zipfile.ZipFile(destination, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(files + [ROOT / 'MANIFEST.json']):
            info = zipfile.ZipInfo(ROOT.name + '/' + path.relative_to(ROOT).as_posix(), (2026,11,10,0,0,0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    print(json.dumps({'archive': str(destination), 'bytes': destination.stat().st_size,
                      'sha256': hashlib.sha256(destination.read_bytes()).hexdigest(),
                      'file_count': len(files) + 1}, indent=2))


if __name__ == '__main__':
    main()
