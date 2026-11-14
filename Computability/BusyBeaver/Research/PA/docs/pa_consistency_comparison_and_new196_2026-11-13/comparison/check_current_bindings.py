#!/usr/bin/env python3
"""Rebind the existing comparative audit to the current pinned ZIP bytes.

This does not certify arithmetic soundness. It checks exact source identities,
including every original accepted U208 presentation used in the audit.
"""
import argparse
import hashlib
import json
from pathlib import Path
from zipfile import ZipFile


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--incoming', type=Path, required=True)
    ap.add_argument('--comparison', type=Path, required=True)
    ap.add_argument('--busybeaver', type=Path, required=True)
    ap.add_argument('--busybeaver209', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    manifest = json.loads((args.comparison / 'inputs/manifest.json').read_text())
    zips = {}
    records = []
    for item in manifest['tables']:
        local = (args.comparison / 'inputs' / item['file']).read_bytes()
        assert sha(local) == item['sha256']
        if 'archive' in item:
            archive = item['archive']
            if archive not in zips:
                raw = (args.incoming / archive).read_bytes()
                assert sha(raw) == item['archive_sha256'], archive
                zips[archive] = ZipFile(args.incoming / archive)
            original = zips[archive].read(item['member'])
            assert original == local, item['id']
            origin = archive + '::' + item['member']
        elif item['id'] == 'pa196':
            original = (args.busybeaver / 'data/pa196.tm').read_bytes()
            assert original == local
            origin = 'jamesyc/BusyBeaver@407cdc356f6b586635e71ac92be394255f4bfea4/data/pa196.tm'
        elif item['id'] == 'pa209':
            original = (args.busybeaver209 / 'data/pa209.tm').read_bytes()
            assert original == local
            origin = 'jamesyc/BusyBeaver@69d98241a721ead20b4f0b17df9062950b40fbfe/data/pa209.tm'
        else:
            raise ValueError('Missing original binding: ' + item['id'])
        records.append({'id': item['id'], 'sha256': sha(local), 'origin': origin,
                        'byte_identity': True})
    for item in manifest.get('incoming_research_status', []):
        archive = item['archive']
        if archive not in zips:
            raw = (args.incoming / archive).read_bytes()
            assert sha(raw) == item['archive_sha256'], archive
            zips[archive] = ZipFile(args.incoming / archive)
        raw = zips[archive].read(item['status_member'])
        assert sha(raw) == item['status_sha256'], archive
    inventory = []
    for path in sorted(args.incoming.glob('*.zip')):
        with ZipFile(path) as z:
            names = z.namelist()
            statuses = sorted((n for n in names if Path(n).name.lower().startswith('readme')
                               and not n.endswith('/')), key=lambda n: (n.count('/'),len(n)))
            entry = {'archive': path.name, 'sha256': sha(path.read_bytes()),
                     'members': len(names), 'tm_members': sum(n.endswith('.tm') for n in names)}
            if statuses:
                raw = z.read(statuses[0])
                entry.update(status_member=statuses[0], status_sha256=sha(raw),
                             status_start=raw.decode(errors='replace')[:1600])
            inventory.append(entry)
    result = {'claim': 'Exact input identity only',
              'proveit_commit': 'dc523e7b06ffb414093c90aa035500ca283e5f75',
              'tables': records, 'archive_inventory': inventory,
              'audited_original_zip_count': len(zips), 'all_checks_passed': True}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'tables_bound':len(records),'all_archives':len(inventory),
                      'audited_original_zip_count':len(zips),'passed':True}, indent=2))


if __name__ == '__main__':
    main()
