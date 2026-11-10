"""Make a checked, deterministic ZIP payload with an integrity manifest."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent


def payload():
    return sorted(p for p in ROOT.rglob('*') if p.is_file()
                  and '__pycache__' not in p.parts
                  and not p.name.endswith(('.pyc', '.aux', '.log', '.out', '.toc', '.fls', '.fdb_latexmk'))
                  and p.name != 'MANIFEST.json')


def main():
    files = payload()
    entries = [{'path': p.relative_to(ROOT).as_posix(),
                'bytes': p.stat().st_size,
                'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]
    manifest = ROOT / 'MANIFEST.json'
    manifest.write_text(json.dumps({
        'package': ROOT.name,
        'source_commit': '70feebabe24445912ae5eb336a6d7e9ba40a882b',
        'files': entries,
        'note': 'Verify before rebuilding. PDF build bytes and regenerated receipts can vary with tool versions.'
    }, indent=2) + '\n')
    archive = ROOT.parent / (ROOT.name + '.zip')
    with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as target:
        for p in sorted(files + [manifest]):
            entry = zipfile.ZipInfo(ROOT.name + '/' + p.relative_to(ROOT).as_posix(),
                                   date_time=(2026, 11, 9, 12, 0, 0))
            entry.external_attr = 0o100644 << 16
            entry.compress_type = zipfile.ZIP_DEFLATED
            target.writestr(entry, p.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(archive) as check:
        if check.testzip() is not None:
            raise ValueError('Archive CRC failure')
        for entry in entries:
            value = check.read(ROOT.name + '/' + entry['path'])
            if hashlib.sha256(value).hexdigest() != entry['sha256']:
                raise ValueError('Archive payload mismatch: ' + entry['path'])
    print(json.dumps({'archive': str(archive), 'files': len(entries) + 1,
                      'bytes': archive.stat().st_size,
                      'sha256': hashlib.sha256(archive.read_bytes()).hexdigest(),
                      'crc_and_all_payload_hashes': 'PASS'}, indent=2))


if __name__ == '__main__':
    main()
