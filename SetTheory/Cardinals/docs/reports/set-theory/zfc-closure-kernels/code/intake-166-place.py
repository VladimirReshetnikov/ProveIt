#!/usr/bin/env python3
"""Place source70 from committed bytes; caller alone stages/retires/commits.

No supplied program is imported or executed. All 191 members are recovered to
a new external directory; only the 170 explicitly mapped ancillary files are
copied to absent repository destinations. No checksum manifest is verified.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import io
import json
import stat
import subprocess
import zipfile

MAP_SHA = 'c0fdae49d82a5cef50188b6a16b7c36cb6b43f3f6453034dfe4793e5128cedfc'

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args])

def relative(name):
    p = PurePosixPath(name)
    require(bool(p.parts) and not p.is_absolute() and '..' not in p.parts
            and '\\' not in name and ':' not in name and '\n' not in name
            and '\r' not in name, 'Unsafe path: ' + name)
    return p

def payloads(raw):
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
    return files

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--map', type=Path, default=Path(__file__).with_name('placement-proposal.json'))
    args = ap.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    require(not output.exists() and output != repo and repo not in output.parents, 'Output must be new and external')
    require(sha(args.map.read_bytes()) == MAP_SHA, 'Placement map identity')
    plan = json.loads(args.map.read_text())
    arc = plan['archive']
    raw = git(repo, 'show', arc['arrival'] + ':' + arc['archive'])
    require(sha(raw) == arc['archive_sha256'] and blob(raw) == arc['archive_blob']
            and len(raw) == arc['archive_bytes'], 'Committed archive identity')
    require((repo / arc['archive']).read_bytes() == raw, 'Current ZIP differs from arrival')
    files = payloads(raw)
    require(len(files) == 191 and len(plan['files']) == 191
            and {x['archive_member'] for x in plan['files']} == set(files), 'Complete member census')
    selected = []
    for row in plan['files']:
        data = files[row['archive_member']]
        require(sha(data) == row['sha256'] and blob(data) == row['git_blob']
                and len(data) == row['bytes'], 'Member identity: ' + row['archive_member'])
        if row['disposition'] == 'place_unchanged':
            relative(row['target'])
            dest = repo / row['target']
            require(repo in dest.resolve().parents and not dest.exists() and not dest.is_symlink(), 'Unsafe or existing target: ' + str(dest))
            selected.append(row)
        else:
            require(row['disposition'] == 'archive_only', 'Unknown disposition')
    require(len(selected) == 170 and len({x['target'] for x in selected}) == 170, 'Placed census')
    require(plan['retire_only_after_exact_placement'] == [arc['archive']], 'Retirement scope')
    output.mkdir()
    fresh = output / 'fresh-extraction'
    fresh.mkdir()
    for name, data in files.items():
        target = fresh.joinpath(*relative(name).parts)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    for row in selected:
        source = fresh.joinpath(*relative(row['archive_member']).parts)
        dest = repo / row['target']
        dest.parent.mkdir(parents=True, exist_ok=True)
        with dest.open('xb') as stream:
            stream.write(source.read_bytes())
        require(dest.read_bytes() == files[row['archive_member']], 'Written byte mismatch')
    written = [x['target'] for x in selected]
    (output / 'stage-paths.txt').write_text('\n'.join(written) + '\n')
    (output / 'retire-paths.txt').write_text(arc['archive'] + '\n')
    record = {
        'status': 'PLACED_BYTES_VERIFIED_NOT_STAGED_OR_COMMITTED',
        'batch': 166, 'host_source': 70, 'map_sha256': MAP_SHA,
        'repo_head': git(repo, 'rev-parse', 'HEAD').decode().strip(),
        'archive': arc, 'source_members': 191, 'placed': 170, 'archive_only': 21,
        'written': written, 'retire_only_after_staging_exact_files': [arc['archive']],
        'fresh_extraction': str(fresh), 'proof_or_supplied_execution': False,
        'git_mutations': False, 'checksum_manifest_verification': False,
    }
    (output / 'placement.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'status': record['status'], 'placed': 170, 'output': str(output)}))

if __name__ == '__main__':
    main()
