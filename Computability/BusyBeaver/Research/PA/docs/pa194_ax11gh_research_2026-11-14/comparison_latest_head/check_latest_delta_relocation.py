#!/usr/bin/env python3
"""Read-only Git audit: filed packet files equal already audited ZIP members.

This checks content identities, not the claims or validity of the machines.
It deliberately does not audit the separate newly arriving frontier ZIP.
"""
from pathlib import Path
import argparse
import hashlib
import io
import json
import subprocess
import zipfile

PACKETS = (
    'pa194_ax11g_research_2026-11-14',
    'pa194_ax11h_research_2026-11-14',
    'pa194_ax11qh4_research_2026-11-14',
    'pa194gh_research_2026-11-14',
)
PREFIX = 'Computability/BusyBeaver/Research/PA/docs/'


def audit(repo, old, new):
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=repo)
    changed = [line.split('\t') for line in git(
        'diff', '--name-status', '--no-renames', old, new).decode().splitlines()]
    blobs = {}
    for entry in git('ls-tree', '-r', '-z', new).split(b'\0'):
        if entry:
            meta, path = entry.split(b'\t', 1)
            blobs[path.decode()] = meta.split()[2].decode()
    imports, known, mismatches = [], set(), []
    for packet in PACKETS:
        archive = git('show', f'{old}:docs/incoming/{packet}.zip')
        members = {}
        with zipfile.ZipFile(io.BytesIO(archive)) as zf:
            for info in zf.infolist():
                if info.is_dir():
                    continue
                key = info.filename.split('/', 1)[1]
                data = zf.read(info)
                members[key] = hashlib.sha1(
                    f'blob {len(data)}\0'.encode() + data).hexdigest()
        suffix = '_2' if packet.startswith('pa194_ax11h_') else ''
        destination = PREFIX + packet + suffix + '/'
        added = [p for status, p in changed if status == 'A' and p.startswith(destination)]
        errors = []
        for path in added:
            rel = path[len(destination):]
            known.add(path)
            if blobs[path] != members.get(rel):
                errors.append(dict(path=path, member_found=rel in members,
                                   new_blob=blobs[path], zip_blob=members.get(rel)))
        imports.append(dict(archive=packet + '.zip',
                            archive_sha256=hashlib.sha256(archive).hexdigest(),
                            destination=destination, added_files=len(added),
                            added_tm_json=sum(p.endswith(('.tm', '.json')) for p in added),
                            all_added_equal_original_zip_members=not errors,
                            differences=errors))
        mismatches.extend(errors)
    return dict(old=old, new=new, scope='all repository paths, no checkout modifications',
                total_changed_paths=len(changed), four_archive_imports=imports,
                other_tm_json_zip_changes=[dict(status=s, path=p, blob=blobs.get(p))
                    for s, p in changed if p not in known and p.endswith(('.tm', '.json', '.zip'))],
                other_added_paths=[p for s, p in changed if s == 'A' and p not in known],
                mismatches=mismatches)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', required=True, type=Path)
    p.add_argument('--old', default='1e1a41f799d4658b829cdd0eabae3775a0c8c4a0')
    p.add_argument('--new', default='19b9ea945cc95fe25535d44d949904843f4a824a')
    p.add_argument('--output', required=True, type=Path)
    a = p.parse_args()
    result = audit(a.repo, a.old, a.new)
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'imported_files': sum(x['added_files'] for x in result['four_archive_imports']),
                      'mismatches': result['mismatches'],
                      'other_tm_json_zip_changes': result['other_tm_json_zip_changes']}, indent=2))
    raise SystemExit(bool(result['mismatches']))
