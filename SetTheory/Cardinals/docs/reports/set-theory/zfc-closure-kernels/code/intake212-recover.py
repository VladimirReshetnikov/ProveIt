#!/usr/bin/env python3
# SPDX-License-Identifier: MIT-0
"""Recover batch212 from exact placed bytes and immutable Git references.

This own intake helper treats the arrival archive and every payload as data.
It invokes no delivered program, compiler or checksum-manifest suite.
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
ARRIVAL = '6f0d42d368506bc29c70ace1c992ed88b2651346'
ARCHIVE = 'docs/incoming/K215_Checked_Affine_Core_and_CM215_2026-10-21.zip'
ARCHIVE_SHA = '1ec6a980c4e350dfe9e2642c2a3d9b137374b75029ed274523fc1ca2f24666e2'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def safe(name):
    p = PurePosixPath(name)
    require(not p.is_absolute() and '..' not in p.parts and '\\' not in name
            and '\n' not in name and '\r' not in name
            and not re.match(r'^[A-Za-z]:', name), 'Unsafe path: ' + name)
    return name

class Git:
    def __init__(self, repo):
        self.proc = subprocess.Popen(['git', '-C', str(repo), 'cat-file', '--batch'],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        self.cache = {}

    def read(self, commit, path):
        require(re.fullmatch('[0-9a-f]{40}', commit) is not None, 'Non-immutable Git reference')
        query = commit + ':' + safe(path)
        if query in self.cache:
            return self.cache[query]
        self.proc.stdin.write((query + '\n').encode())
        self.proc.stdin.flush()
        fields = self.proc.stdout.readline().decode().strip().split()
        require(len(fields) == 3 and fields[1] == 'blob', 'Missing Git blob: ' + query)
        data = self.proc.stdout.read(int(fields[2]))
        require(len(data) == int(fields[2]) and self.proc.stdout.read(1) == b'\n', 'Truncated Git response')
        self.cache[query] = data
        return data

    def close(self):
        self.proc.stdin.close()
        self.proc.stdout.close()
        require(self.proc.wait(timeout=10) == 0, 'Git reader failed')

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, default=Path.cwd())
    ap.add_argument('--map', type=Path)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--verify-only', action='store_true')
    mode.add_argument('--out', type=Path)
    ap.add_argument('--result', type=Path)
    args = ap.parse_args()
    repo = args.repo.resolve()
    mapping = args.map or repo / HOST / 'data/intake212-placement.json'
    raw_map = mapping.read_bytes()
    m = json.loads(raw_map)
    require((m['batch'], m['source'], m['member_count'], m['member_bytes']) ==
            (212, 179, 862, 11367916), 'Wrong batch/source/member boundary')
    require(m['arrival_commit'] == ARRIVAL and m['archive_path'] == ARCHIVE
            and m['archive_sha256'] == ARCHIVE_SHA, 'Wrong arrival identity')
    g = Git(repo)
    try:
        archive = g.read(ARRIVAL, ARCHIVE)
        require(len(archive) == 2218276 and sha(archive) == ARCHIVE_SHA, 'Arrival bytes changed')
        with zipfile.ZipFile(io.BytesIO(archive)) as z:
            infos = z.infolist()
            names = [safe(i.filename) for i in infos]
            require(len(names) == len(set(names)) == 862, 'Duplicate/missing arrival member')
            require(all(not i.is_dir() and not (i.flag_bits & 1)
                        and ((i.external_attr >> 16) & 0o170000) != 0o120000
                        for i in infos), 'Unsupported archive member')
            rows = m['members']
            require([r['member'] for r in rows] == names, 'Missing/reordered map member')
            recovered = {}
            for row in rows:
                name = row['member']
                route = row['route']
                if route == 'git':
                    data = g.read(row['commit'], row['path'])
                elif route == 'placed':
                    path = repo / safe(row['path'])
                    require(path.is_file() and not path.is_symlink(), 'Missing placed member: ' + str(path))
                    data = path.read_bytes()
                elif route == 'arrival_member':
                    data = z.read(name)
                elif route == 'delivery_member':
                    require(row['target_member'] in recovered, 'Forward/unknown delivery alias')
                    data = recovered[row['target_member']]
                else:
                    raise ValueError('Unknown route: ' + route)
                require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'Member bytes changed: ' + name)
                require(data == z.read(name), 'Recovery differs from arrival: ' + name)
                recovered[name] = data
            counts = dict(Counter(r['route'] for r in rows))
            require(counts == m['counts'], 'Route count mismatch')
            require(sum(map(len, recovered.values())) == 11367916, 'Total byte count mismatch')
            if args.out:
                require(not args.out.exists(), 'Output directory already exists')
                for name, data in recovered.items():
                    target = args.out / name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(data)
    finally:
        g.close()
    result = {'status':'PASS_EXACT_862_MEMBER_RECOVERY', 'batch':212, 'source':179,
              'map_sha256':sha(raw_map), 'helper_sha256':sha(Path(__file__).read_bytes()),
              'archive_sha256':ARCHIVE_SHA, 'members':862, 'bytes':11367916,
              'routes':counts, 'mode':'reconstruct' if args.out else 'verify_only',
              'output':str(args.out) if args.out else None,
              'supplied_code_or_compiler_executed':False}
    if args.result:
        args.result.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
