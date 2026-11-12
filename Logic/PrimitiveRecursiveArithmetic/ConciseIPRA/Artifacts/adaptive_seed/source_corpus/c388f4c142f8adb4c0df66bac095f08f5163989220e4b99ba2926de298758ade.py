"""Create a clean deliverable ZIP and a SHA-256 payload manifest."""
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent
EXCLUDED = {'.aux', '.log', '.out', '.toc', '.fls', '.fdb_latexmk', '.synctex.gz', '.pyc'}


def payload():
    return [p for p in sorted(ROOT.rglob('*')) if p.is_file()
            and '__pycache__' not in p.parts and p.suffix not in EXCLUDED
            and p.name != 'payload_sha256.json']


def main():
    paths = payload()
    manifest = [{'file': str(p.relative_to(ROOT)), 'size': p.stat().st_size,
                 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths]
    record = ROOT / 'payload_sha256.json'
    record.write_text(json.dumps(manifest, indent=2) + '\n')
    target = ROOT.parent / (ROOT.name + '.zip')
    with zipfile.ZipFile(target, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in [*paths, record]:
            archive.write(path, str(Path(ROOT.name) / path.relative_to(ROOT)))
    with zipfile.ZipFile(target) as archive:
        if archive.testzip() is not None:
            raise RuntimeError('Archive CRC failure')
    print(json.dumps({'archive': str(target), 'files': len(paths) + 1,
                      'size': target.stat().st_size,
                      'sha256': hashlib.sha256(target.read_bytes()).hexdigest()}, indent=2))


if __name__ == '__main__':
    main()
