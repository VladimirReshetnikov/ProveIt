#!/usr/bin/env python3
"""Recover source71's 1044 original members and compare all 1007 placed ancillary files.

Only committed bytes are restored. No checker, simulator, compiler or builder
is invoked, and delivery checksum manifests are not verified.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import io
import json
import stat
import subprocess
import zipfile

MAP_SHA = '71bfcbc1b859b2be6609f735e265fcd9e659e4e5355b095eb9251583c2408307'
HOST = Path('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels')

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def relative(name):
    p = PurePosixPath(name)
    require(bool(p.parts) and not p.is_absolute() and '..' not in p.parts
            and '\\' not in name and ':' not in name and '\n' not in name
            and '\r' not in name, 'Unsafe path: ' + name)
    return p

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--map', type=Path)
    args = ap.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    mp = args.map or repo / HOST / 'data/intake-167-placement.json'
    require(not output.exists() and output != repo and repo not in output.parents, 'Output must be new and external')
    require(sha(mp.read_bytes()) == MAP_SHA, 'Placement map identity')
    plan = json.loads(mp.read_text())
    arc = plan['archive']
    raw = subprocess.check_output(['git', '-C', str(repo), 'show', arc['arrival'] + ':' + arc['archive']])
    require(sha(raw) == arc['archive_sha256'] and blob(raw) == arc['archive_blob']
            and len(raw) == arc['archive_bytes'], 'Committed archive identity')
    files = {}
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        require(sum(x.file_size for x in archive.infolist()) < 500_000_000, 'Archive size limit')
        for entry in archive.infolist():
            relative(entry.filename)
            require(not stat.S_ISLNK(entry.external_attr >> 16), 'Archive symlink')
            if entry.is_dir():
                continue
            require(entry.filename not in files, 'Duplicate archive member')
            files[entry.filename] = archive.read(entry)
    require(len(files) == 1044 and len(plan['files']) == 1044
            and {x['archive_member'] for x in plan['files']} == set(files), 'Complete member census')
    compared = []
    for row in plan['files']:
        data = files[row['archive_member']]
        require(sha(data) == row['sha256'] and blob(data) == row['git_blob']
                and len(data) == row['bytes'], 'Member identity: ' + row['archive_member'])
        if row['disposition'] == 'place_unchanged':
            relative(row['target'])
            target = repo / row['target']
            require(repo in target.resolve().parents and target.read_bytes() == data, 'Placed byte mismatch: ' + row['target'])
            compared.append(row['target'])
        else:
            require(row['disposition'] == 'archive_only', 'Unknown disposition')
    require(len(compared) == 1007 and len(set(compared)) == 1007, 'Placed census')
    output.mkdir()
    for name, data in files.items():
        target = output.joinpath(*relative(name).parts)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    package = output / 'zfc244-loop-rotation-20261018'
    record = {
        'status': 'RECOVERED_AND_PLACED_BYTES_MATCH', 'batch': 167, 'host_source': 71,
        'map_sha256': MAP_SHA, 'archive': arc, 'files_recovered': 1044,
        'placed_pairs_compared': 1007, 'archive_only': 37, 'package_root': str(package),
        'supplied_execution': False, 'checksum_manifest_verification': False,
    }
    (output / 'recovery.json').write_text(json.dumps(record, indent=2) + '\n')
    print(package)
    print(json.dumps({'status': record['status'], 'files': 1044, 'placed_pairs': 1007}))

if __name__ == '__main__':
    main()
