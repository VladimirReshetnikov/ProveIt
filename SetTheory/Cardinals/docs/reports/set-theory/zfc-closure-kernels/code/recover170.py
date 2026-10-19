#!/usr/bin/env python3
"""Recover the original intake170 layout and verify every maintained alias; execute no supplied code."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, io, json, stat, subprocess, zipfile

MAP = 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake170-placement.json'
MAP_SHA = '16863862ecb3450d3bcb5c38c4b6ed09672fdf98facd947b2ab0b7e49938320f'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def safe(name):
    p = PurePosixPath(name)
    require(p.parts and not p.is_absolute() and '..' not in p.parts
            and not any(c in name for c in '\\\r\n:'), 'Unsafe member or target')
    return p

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args(); repo, out = a.repo.resolve(), a.output.resolve()
    require(not out.exists() and not out.is_relative_to(repo) and not repo.is_relative_to(out), 'Use fresh external output')
    rawmap = (repo / MAP).read_bytes()
    require(sha(rawmap) == MAP_SHA, 'Placement map differs')
    p = json.loads(rawmap)
    require(p['status'] == 'ROOT_FRESH_EXACT_PLACEMENT_AND_RETIREMENT_PASS' and p['batch'] == 170 and len(p['retired']) == 1 and len(p['files']) == 79, 'Wrong actual placement')
    require(all(row['source'] == 80 for row in p['files']), 'Wrong source')
    sources_spec = [dict(host_source=80, archive=p['retired'][0], files=p['files'])]
    files, checked, sources = {}, [], []
    for s in sources_spec:
        arc = s['archive']; safe(arc['path'])
        raw = subprocess.check_output(['git', '-C', str(repo), 'show', arc['arrival'] + ':' + arc['path']])
        require(sha(raw) == arc['sha256'] and blob(raw) == arc['git_blob'], 'Arrival archive differs')
        members = {}
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            require(sum(e.file_size for e in z.infolist()) < 100_000_000, 'Expanded-size cap')
            for e in z.infolist():
                safe(e.filename); require(not stat.S_ISLNK(e.external_attr >> 16), 'Symlink member')
                if e.is_dir():
                    continue
                require(e.filename not in members, 'Duplicate member')
                members[e.filename] = z.read(e)
        require(set(members) == {r['archive_member'] for r in s['files']}, 'Original member census')
        directory = out / ('source' + str(s['host_source']))
        for r in s['files']:
            data = members[r['archive_member']]
            require(sha(data) == r['sha256'] and blob(data) == r['git_blob'], 'Original member differs')
            target = directory / safe(r['archive_member'])
            require(target not in files, 'Recovery collision'); files[target] = data
            if r['disposition'] == 'archive_only':
                continue
            require(r['disposition'] in ('place_unchanged', 'reuse_existing_unchanged', 'reuse_batch_unchanged'), 'Unknown disposition')
            maintained = repo / safe(r['target'])
            require(maintained.resolve().is_relative_to(repo) and maintained.read_bytes() == data, 'Maintained member/alias differs')
            checked.append(r['target'])
        sources.append(dict(source=s['host_source'], archive=arc['path'], destination=str(directory), members=len(members)))
    require(len(files) == 79 and len(checked) == 73 and len(set(checked)) == 67, 'Recovery census')
    out.mkdir()
    for path, data in files.items():
        path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(data)
    result = dict(status='ORIGINAL_SOURCE80_LAYOUT_RECOVERED_AND_ALL_MAINTAINED_ALIASES_MATCH',
                  members=79, maintained_occurrences=73, distinct_maintained_targets=67,
                  archive_only=6, map_sha256=MAP_SHA, sources=sources, output=str(out),
                  supplied_execution=False, checksum_manifest_validation=False)
    (out / 'recovery.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
