#!/usr/bin/env python3
"""Authenticate retained source archives and copied predecessor interfaces."""
from pathlib import Path
import hashlib
import json
import stat
import zipfile

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    ledger = json.loads((ROOT/'baseline/FETCH_LEDGER.json').read_text())
    entries = {entry['path']:entry for entry in ledger['files']}
    retained = [
        ('ConZFC_13_Integer_Norms_2026-10-24.zip', 'baseline/ConZFC_13_Integer_Norms_2026-10-24'),
        ('con-zfc-parity-norms-2026-10-23.zip', 'finalizers/source'),
    ]
    receipts = []
    for name, destination in retained:
        path = ROOT/'baseline'/name
        raw = path.read_bytes()
        entry = entries[name]
        require(len(raw) == entry['bytes'], 'Source archive size: '+name)
        require(hashlib.sha256(raw).hexdigest() == entry['sha256'], 'Source archive SHA256: '+name)
        git = hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(git == entry['git_blob'], 'Source archive Git blob: '+name)
        matched = 0
        with zipfile.ZipFile(path) as archive:
            require(archive.testzip() is None, 'Source archive CRC: '+name)
            for member in archive.infolist():
                relative = Path(member.filename)
                require(not relative.is_absolute() and '..' not in relative.parts and
                        not stat.S_ISLNK(member.external_attr >> 16), 'Unsafe ZIP source path')
                if member.is_dir():
                    continue
                source = ROOT/destination/relative
                require(source.is_file() and source.read_bytes() == archive.read(member),
                        'Copied source differs from pinned original: '+str(relative))
                matched += 1
        receipts.append({'archive':name, 'sha256':entry['sha256'], 'git_blob':git,
                         'url':entry['url'], 'unchanged_source_files':matched})
    inherited = json.loads((ROOT/'alternative/PROVENANCE.json').read_text())
    for name, expected in inherited['sha256'].items():
        path = ROOT/'provenance/certificate_predecessor'/name
        require(hashlib.sha256(path.read_bytes()).hexdigest() == expected,
                'Alternative predecessor source: '+name)
    print(json.dumps({'status':'PASS', 'archives':receipts,
                      'alternative_predecessor_files':len(inherited['sha256']),
                      'boundary':'Source identity, not semantic calibration.'}, indent=2))


if __name__ == '__main__':
    main()
