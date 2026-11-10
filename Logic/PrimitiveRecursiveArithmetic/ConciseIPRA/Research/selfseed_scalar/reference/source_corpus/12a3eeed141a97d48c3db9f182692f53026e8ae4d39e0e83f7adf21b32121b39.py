"""Create a clean, deterministic ZIP and verify every payload hash and CRC."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent


def payload():
    return sorted(p for p in ROOT.rglob('*') if p.is_file()
                  and '_build' not in p.relative_to(ROOT).parts
                  and '__pycache__' not in p.relative_to(ROOT).parts
                  and p.name != 'MANIFEST.json'
                  and p.suffix not in {'.pyc', '.aux', '.log', '.out', '.toc'})


def main():
    files = payload()
    records = [{'path': p.relative_to(ROOT).as_posix(),
                'bytes': p.stat().st_size,
                'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
               for p in files]
    manifest = ROOT / 'MANIFEST.json'
    manifest.write_text(json.dumps({'algorithm': 'SHA-256', 'files': records}, indent=2) + '\n')
    archive = ROOT.parent / (ROOT.name + '.zip')
    with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in [*files, manifest]:
            info = zipfile.ZipInfo(ROOT.name + '/' + p.relative_to(ROOT).as_posix(),
                                   date_time=(2026, 11, 9, 12, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            z.writestr(info, p.read_bytes())
    with zipfile.ZipFile(archive) as z:
        if z.testzip() is not None:
            raise RuntimeError('ZIP CRC failure')
        for entry in records:
            data = z.read(ROOT.name + '/' + entry['path'])
            if hashlib.sha256(data).hexdigest() != entry['sha256']:
                raise RuntimeError('ZIP payload mismatch: ' + entry['path'])
    print(json.dumps({'archive': str(archive), 'bytes': archive.stat().st_size,
                      'sha256': hashlib.sha256(archive.read_bytes()).hexdigest(),
                      'payload_files': len(records), 'crc_and_hashes': 'PASS'}, indent=2))


if __name__ == '__main__':
    main()
