#!/usr/bin/env python3
"""Verify exact recovery of supplemental206 or207 without an output tree.

Read immutable Git paths, supplemental raw files and original arrival ZIPs.
Compare every recovered member directly with its original ZIP member as well
as the map's size/SHA256/Git blob. No supplied code or checksum manifest runs.
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
CONFIGS = {
    206: ('53269bcab1efc0f82d3022645bd7cf0c22d84959', '69e6d97fc2ea6da87b718109b1c8614a0927a621', 174, 360, 4255981),
    207: ('beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc', '62f0f95e2b2df5b380ae502eb65bd64f1ee90209', 175, 1132, 19425247),
}

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
            and '\n' not in path and '\r' not in path, 'Unsafe path: ' + path)
    return path

class GitBlobs:
    def __init__(self, repo):
        self.proc = subprocess.Popen(['git', '-C', str(repo), 'cat-file', '--batch'],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def read(self, commit, path):
        require(re.fullmatch('[0-9a-f]{40}', commit) is not None, 'Commit must be a full Git ID')
        query = commit + ':' + safe(path)
        self.proc.stdin.write((query + '\n').encode())
        self.proc.stdin.flush()
        header = self.proc.stdout.readline().decode().strip().split()
        require(len(header) == 3 and header[1] == 'blob', 'Missing Git blob: ' + query)
        data = self.proc.stdout.read(int(header[2]))
        require(len(data) == int(header[2]) and self.proc.stdout.read(1) == b'\n', 'Truncated Git response')
        require(blob(data) == header[0], 'Git blob identity mismatch')
        return header[0], data

    def close(self):
        self.proc.stdin.close()
        self.proc.stdout.close()
        require(self.proc.wait(timeout=10) == 0, 'Git reader failed')

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, default=Path.cwd())
    ap.add_argument('--map', type=Path, required=True)
    ap.add_argument('--nested-inventory', type=Path)
    ap.add_argument('--verify-only', action='store_true', required=True,
                    help='Required; this helper never materializes an output tree')
    ap.add_argument('--result', type=Path, help='Optional own JSON receipt; must not already exist')
    args = ap.parse_args()
    repo = Path(subprocess.check_output(['git', '-C', str(args.repo), 'rev-parse', '--show-toplevel'],
                                        text=True).strip())
    mapping = args.map
    map_bytes = mapping.read_bytes()
    self_bytes = Path(__file__).read_bytes()
    plan = json.loads(map_bytes)
    require(plan['schema'] == 2 and plan['batch'] in CONFIGS, 'Wrong map schema or batch')
    batch = plan['batch']
    ARRIVAL, PLACEMENT, source_id, member_count, expanded_bytes = CONFIGS[batch]
    require(plan['arrival_commit'] == ARRIVAL and plan['upstream_placement_commit'] == PLACEMENT,
            'Wrong arrival/placement provenance')
    require([s['source'] for s in plan['sources']] == [source_id], 'Wrong source numbering')
    require([s['archive_index'] for s in plan['sources']] == [0], 'Wrong archive ordering')
    rows = plan['members']
    nested_path = args.nested_inventory or repo / HOST / 'data/intake206207-nested-inventory.json'
    nested_bytes = nested_path.read_bytes()
    nested_records = [r for r in json.loads(nested_bytes)['archives'] if r['batch'] == batch]
    require(len(nested_records) == plan['nested_archive_count'], 'Wrong nested archive count')
    require(len(rows) == member_count and sum(r['bytes'] for r in rows) == expanded_bytes,
            'Wrong original member census')
    require(len({(r['archive_index'], r['member']) for r in rows}) == member_count, 'Duplicate map row')
    if args.result:
        require(not args.result.exists(), 'Receipt path already exists')
    git = GitBlobs(repo)
    counts, classes = Counter(), Counter()
    per_source, supplemental, nested_checked = [], {}, []
    transcript = hashlib.sha256()
    try:
        for source in plan['sources']:
            require(source['arrival_commit'] == ARRIVAL, 'Wrong source arrival')
            archive_oid, raw = git.read(ARRIVAL, source['archive'])
            require(archive_oid == source['archive_git_blob'] and len(raw) == source['archive_bytes']
                    and sha(raw) == source['archive_sha256'], 'Archive identity mismatch')
            with zipfile.ZipFile(io.BytesIO(raw)) as archive:
                infos = [i for i in archive.infolist() if not i.is_dir()]
                names = [safe(i.filename) for i in infos]
                require(len(names) == len(set(names)), 'Repeated ZIP member name')
                require(all(((i.external_attr >> 16) & 0o170000) != 0o120000 for i in infos),
                        'ZIP symlink rejected')
                selected = [r for r in rows if r['archive_index'] == source['archive_index']]
                require(set(names) == {r['member'] for r in selected}, 'Map/ZIP member-set mismatch')
                require(len(selected) == source['member_count'] and
                        sum(r['bytes'] for r in selected) == source['expanded_bytes'], 'Source census mismatch')
                for entry in nested_records:
                    chain = entry['chain']
                    require(bool(chain), 'Empty nested archive chain')
                    nested_data = archive.read(safe(chain[0]))
                    for name in chain[1:]:
                        with zipfile.ZipFile(io.BytesIO(nested_data)) as parent:
                            nested_data = parent.read(safe(name))
                    require(len(nested_data) == entry['archive_bytes'] and
                            sha(nested_data) == entry['archive_sha256'] and
                            blob(nested_data) == entry['archive_git_blob'], 'Nested ZIP identity mismatch')
                    with zipfile.ZipFile(io.BytesIO(nested_data)) as child:
                        child_infos = [i for i in child.infolist() if not i.is_dir()]
                        child_names = [safe(i.filename) for i in child_infos]
                        require(len(child_names) == len(set(child_names)) == entry['member_count'],
                                'Nested member census mismatch')
                        require(all(((i.external_attr >> 16) & 0o170000) != 0o120000 for i in child_infos),
                                'Nested ZIP symlink rejected')
                        require(set(child_names) == {r['member'] for r in entry['members']},
                                'Nested member-set mismatch')
                        for inner in entry['members']:
                            data = child.read(inner['member'])
                            require(len(data) == inner['bytes'] and sha(data) == inner['sha256'] and
                                    blob(data) == inner['git_blob'], 'Nested member identity mismatch')
                    nested_checked.append({'chain': chain, 'members': entry['member_count'],
                                           'archive_git_blob': entry['archive_git_blob'], 'status': 'PASS'})
                local = Counter()
                for row in selected:
                    require(row['source'] == source['source'], 'Wrong source on member')
                    original = archive.read(row['member'])
                    route = row['recovery']
                    kind = route['kind']
                    if kind == 'git-path':
                        actual_oid, recovered = git.read(route['commit'], route['path'])
                        require(actual_oid == route['git_blob'] == row['git_blob'], 'Reference blob mismatch')
                    elif kind == 'supplemental-file':
                        p = safe(route['path'])
                        require(re.fullmatch(re.escape(HOST) + r'/(code|data)/intake20[67]-source17[45]/.+', p)
                                is not None, 'Supplemental path outside owned scope')
                        target = repo / p
                        require(target.is_file() and not target.is_symlink(), 'Missing regular supplemental file')
                        require(target.resolve().is_relative_to(repo.resolve()), 'Supplemental path escapes repo')
                        recovered = target.read_bytes()
                        supplemental[p] = sha(recovered)
                    elif kind == 'arrival-zip':
                        recovered = original
                        require(bool(route.get('reason')), 'Arrival fallback lacks an explicit reason')
                    else:
                        raise ValueError('Unknown recovery route: ' + kind)
                    require(recovered == original, 'Recovered bytes differ: ' + row['member'])
                    require(len(recovered) == row['bytes'] and sha(recovered) == row['sha256']
                            and blob(recovered) == row['git_blob'], 'Member identity mismatch: ' + row['member'])
                    # The immutable path annotation is separately checked, including
                    # any original byte differences retained separately.
                    if row['upstream_expected_blob'] is not None:
                        expected_oid, _ = git.read(PLACEMENT, row['upstream_expected_path'])
                        require(expected_oid == row['upstream_expected_blob'], 'Upstream annotation changed')
                        require(row['upstream_expected_exact'] == (expected_oid == row['git_blob']),
                                'Incorrect exact-byte annotation')
                    if 'upstream_exact_reference' in row:
                        ref = row['upstream_exact_reference']
                        exact_oid, exact = git.read(ref['commit'], ref['path'])
                        require(exact_oid == row['git_blob'] and exact == original, 'Incorrect exact alias annotation')
                    counts[kind] += 1
                    local[kind] += 1
                    classes[route.get('class', 'arrival-only')] += 1
                    transcript.update(json.dumps([row['source'], row['member'], row['bytes'], row['sha256'],
                                                  kind, route.get('path')], separators=(',', ':')).encode() + b'\n')
                require(dict(local) == source['recovery_counts'], 'Per-source route count mismatch')
                per_source.append({'source': source['source'], 'members': len(selected),
                                   'expanded_bytes': source['expanded_bytes'], 'recovery_counts': dict(local),
                                   'archive_git_blob': archive_oid, 'status': 'EXACT_ALL_MEMBERS_PASS'})
        require(dict(counts) == plan['counts'] and dict(classes) == plan['class_counts'], 'Route census mismatch')
        require(len(supplemental) == plan['new_payload_files'], 'New-file census mismatch')
        require(sum((repo / p).stat().st_size for p in supplemental) == plan['new_payload_bytes'], 'New-byte census mismatch')
        require(all(sha((repo / p).read_bytes()) == h for p, h in supplemental.items()), 'Supplement changed during recovery')
        require(mapping.read_bytes() == map_bytes and Path(__file__).read_bytes() == self_bytes,
                'Map/helper changed during verification')
        require(nested_path.read_bytes() == nested_bytes, 'Nested inventory changed during verification')
    finally:
        git.close()
    result = {'status': f'EXACT_{member_count}_MEMBER_STREAMING_RECOVERY_PASS', 'batch': batch,
              'arrival_commit': ARRIVAL, 'upstream_placement_commit': PLACEMENT,
              'map_sha256': sha(map_bytes), 'helper_sha256': sha(self_bytes),
              'nested_inventory_sha256': sha(nested_bytes), 'nested_archives': nested_checked,
              'members': member_count, 'expanded_bytes': expanded_bytes,
              'recovery_counts': dict(counts), 'class_counts': dict(classes),
              'new_payload_files': len(supplemental), 'new_payload_bytes': plan['new_payload_bytes'],
              'sources': per_source, 'ordered_verification_transcript_sha256': transcript.hexdigest(),
              'postcheck': f'All supplemental files, map and helper unchanged after all{member_count} comparisons',
              'output_tree_created': False, 'supplied_code_executed': False,
              'scope': 'Exact provenance/recovery only; no compilation, submitted receipt validation, checksum-manifest interpretation or formal-status promotion.'}
    rendered = json.dumps(result, indent=2) + '\n'
    if args.result:
        args.result.parent.mkdir(parents=True, exist_ok=True)
        with args.result.open('x') as f:
            f.write(rendered)
    print(rendered, end='')

if __name__ == '__main__':
    main()
