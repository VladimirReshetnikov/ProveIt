#!/usr/bin/env python3
# SPDX-License-Identifier: MIT-0
"""Verify every batch208 member from immutable Git or exact placed bytes.

No supplied program or checksum manifest is invoked. No recovered tree is
written. Main manuscripts stay recoverable from their original arrival ZIPs.
"""
import argparse
from collections import Counter
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import zipfile

HOST = 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
ARRIVAL = 'aa66d0a33f1f8237a348899eb8095b045a502832'
EXPECTED = {176: (105, 8143711), 177: (106, 1073294), 178: (194, 2752810)}

def require(test, message):
    if not test:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def safe(path):
    p = PurePosixPath(path)
    require(not p.is_absolute() and '..' not in p.parts and '\\' not in path
            and '\n' not in path and '\r' not in path, 'Unsafe path')
    return path

class Git:
    def __init__(self, repo):
        self.p = subprocess.Popen(['git', '-C', str(repo), 'cat-file', '--batch'],
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def read(self, commit, path):
        require(re.fullmatch(r'[0-9a-f]{40}', commit), 'Non-immutable Git reference')
        query = commit + ':' + safe(path)
        self.p.stdin.write((query + '\n').encode())
        self.p.stdin.flush()
        fields = self.p.stdout.readline().decode().strip().split()
        require(len(fields) == 3 and fields[1] == 'blob', 'Missing Git blob: ' + query)
        data = self.p.stdout.read(int(fields[2]))
        require(len(data) == int(fields[2]) and self.p.stdout.read(1) == b'\n', 'Truncated Git response')
        require(blob(data) == fields[0], 'Git object mismatch')
        return data

    def close(self):
        self.p.stdin.close()
        self.p.stdout.close()
        require(self.p.wait(timeout=10) == 0, 'Git reader failed')

def entries(z):
    infos = [i for i in z.infolist() if not i.is_dir()]
    names = [safe(i.filename) for i in infos]
    require(len(set(names)) == len(names), 'Duplicate ZIP names')
    require(all(((i.external_attr >> 16) & 0o170000) != 0o120000 for i in infos),
            'ZIP symlink')
    return names

def nested_records(data, source, chain):
    result = []
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        members = []
        for name in entries(z):
            b = z.read(name)
            members.append(dict(member=name, bytes=len(b), sha256=sha(b), git_blob=blob(b)))
            if name.endswith('.zip'):
                result.extend(nested_records(b, source, chain + [name]))
    result.append(dict(source=source, chain=chain, archive_bytes=len(data),
                       archive_sha256=sha(data), archive_git_blob=blob(data),
                       member_count=len(members), expanded_bytes=sum(x['bytes'] for x in members),
                       members=members))
    return result

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, default=Path.cwd())
    ap.add_argument('--map', type=Path)
    ap.add_argument('--nested-inventory', type=Path)
    ap.add_argument('--verify-only', action='store_true', required=True)
    ap.add_argument('--result', type=Path)
    args = ap.parse_args()
    repo = Path(subprocess.check_output(['git', '-C', str(args.repo), 'rev-parse', '--show-toplevel'], text=True).strip())
    mpath = args.map or repo / HOST / 'data/intake208-placement.json'
    npath = args.nested_inventory or repo / HOST / 'data/intake208-nested-inventory.json'
    mb, nb = mpath.read_bytes(), npath.read_bytes()
    plan, ni = json.loads(mb), json.loads(nb)
    require(plan['schema'] == 2 and plan['batch'] == 208 and plan['arrival_commit'] == ARRIVAL,
            'Wrong intake/provenance')
    require([s['source'] for s in plan['sources']] == list(EXPECTED), 'Wrong source order')
    rows = plan['members']
    require(len(rows) == plan['member_count'] == 405 and
            sum(x['bytes'] for x in rows) == plan['expanded_bytes'] == 11969815,
            'Wrong original census')
    require(len({(x['source'], x['member']) for x in rows}) == 405, 'Duplicate member row')
    if args.result:
        require(not args.result.exists(), 'Existing receipt must be preserved')
    g = Git(repo)
    routes, checked, actual_nested, placed = Counter(), [], [], {}
    digest = hashlib.sha256()
    try:
        for s in plan['sources']:
            sid = s['source']
            require(s['arrival'] == ARRIVAL, 'Wrong archive arrival')
            raw = g.read(ARRIVAL, s['archive'])
            require((len(raw), sha(raw), blob(raw)) ==
                    (s['archive_bytes'], s['archive_sha256'], s['archive_git_blob']), 'Archive identity mismatch')
            selected = [x for x in rows if x['source'] == sid]
            count, size = EXPECTED[sid]
            require((len(selected), sum(x['bytes'] for x in selected)) == (count, size), 'Source census mismatch')
            with zipfile.ZipFile(io.BytesIO(raw)) as z:
                require(set(entries(z)) == {x['member'] for x in selected}, 'Map/ZIP member-set mismatch')
                for x in selected:
                    original = z.read(x['member'])
                    require((len(original), sha(original), blob(original)) ==
                            (x['bytes'], x['sha256'], x['git_blob']), 'Original member identity mismatch')
                    route = x['recovery']; kind = route['kind']
                    if kind == 'arrival-member':
                        recovered = original
                    elif kind == 'git-path':
                        recovered = g.read(route['commit'], route['path'])
                        require(blob(recovered) == route['git_blob'], 'Alias blob mismatch')
                    elif kind == 'placed-file':
                        path = safe(route['path'])
                        require(re.fullmatch(re.escape(HOST) + r'/(code|data)/intake208-source17[678]/[^/]+', path),
                                'Placed file outside owned scope')
                        target = repo / path
                        require(not target.is_symlink(), 'Placed symlink')
                        recovered = target.read_bytes()
                        placed[path] = sha(recovered)
                    else:
                        raise ValueError('Unknown route')
                    require(recovered == original, 'Recovered bytes differ: ' + x['member'])
                    digest.update(str(sid).encode() + b'\0' + x['member'].encode() + b'\0' + recovered)
                    routes[kind] += 1
                    if x['member'].endswith('.zip'):
                        actual_nested.extend(nested_records(original, sid, [x['member']]))
            checked.append(dict(source=sid, members=count, bytes=size, status='PASS'))
    finally:
        g.close()
    require(dict(routes) == plan['route_counts'], 'Recovery-route census mismatch')
    require(len(placed) == plan['new_file_count'] == 39, 'Placed-file census mismatch')
    require(ni['batch'] == 208 and actual_nested == ni['archives'] and
            len(actual_nested) == plan['nested_archive_count'] == 2, 'Nested inventory mismatch')
    require(mpath.read_bytes() == mb and npath.read_bytes() == nb, 'Metadata changed during control')
    for path, identity in placed.items():
        require(sha((repo / path).read_bytes()) == identity, 'Placed input changed during control')
    result = dict(status='PASS', batch=208, verify_only=True, members=405, expanded_bytes=11969815,
                  sources=checked, routes=dict(routes), distinct_placed_files=len(placed),
                  nested=[dict(source=x['source'], chain=x['chain'], members=x['member_count'],
                               archive_sha256=x['archive_sha256']) for x in actual_nested],
                  map_sha256=sha(mb), nested_inventory_sha256=sha(nb),
                  helper_sha256=sha(Path(__file__).read_bytes()), recovered_transcript_sha256=digest.hexdigest(),
                  placed_postchecks=True, supplied_execution=False, proof_compilers_run=False)
    text = json.dumps(result, indent=2) + '\n'
    if args.result:
        args.result.write_text(text)
    print(text, end='')

if __name__ == '__main__':
    main()
