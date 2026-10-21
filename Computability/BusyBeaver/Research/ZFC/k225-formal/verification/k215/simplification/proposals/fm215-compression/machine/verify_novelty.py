#!/usr/bin/env python3
"""Compare FM215 with every .tm blob in a pinned ProveIt ZFC Git tree.

A cached checkout can supply a missing local file only when its Git blob ID
matches the current tree. Every actual file is then independently rehashed as
a Git blob. No historical table is silently passed off as a current input.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
from collections import Counter
from verify_fm215 import HERE, parse, canonical, sha

PIN = 'b6c7087477e51c017003bd729e712c8969733223'
SCOPE = 'Computability/BusyBeaver/Research/ZFC'


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args])


def tree(repo):
    answer = {}
    for line in git(repo, 'ls-tree', '-r', '-z', 'HEAD', SCOPE).split(b'\0'):
        if not line:
            continue
        metadata, path = line.split(b'\t', 1)
        path = path.decode()
        if path.endswith('.tm'):
            answer[path] = metadata.decode().split()[2]
    return answer


def git_blob_sha(path):
    data = path.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', required=True, type=Path)
    ap.add_argument('--cached-repo', type=Path)
    ap.add_argument('--expected-commit', default=PIN)
    ap.add_argument('--output', type=Path, default=HERE / 'novelty_current_tree.json')
    args = ap.parse_args()
    commit = git(args.repo, 'rev-parse', 'HEAD').decode().strip()
    assert commit == args.expected_commit
    current = tree(args.repo)
    cached = tree(args.cached_repo) if args.cached_repo else {}
    target = canonical(parse(HERE / 'fm215.native.tm')[0])[0]
    tables, all_inputs, missing, bad, matches = [], [], [], [], []
    signatures, state_counts = set(), Counter()
    for path, blob in current.items():
        local = args.repo / path
        if not local.exists():
            if args.cached_repo and cached.get(path) == blob and (args.cached_repo / path).exists():
                local = args.cached_repo / path
            else:
                missing.append(path)
                continue
        assert git_blob_sha(local) == blob, ('Unexpected local bytes', path)
        record = {'path': path, 'git_blob': blob, 'sha256': sha(local)}
        all_inputs.append(record)
        try:
            table, start = parse(local)
        except (ValueError, AssertionError, UnicodeError, OSError):
            bad.append(path)
            continue
        state_counts[len(table) // 2] += 1
        if len(table) != 430:
            continue
        sig, count = canonical(table, start)
        if count != 216:
            continue
        signatures.add(sig)
        tables.append(record)
        if target in (sig, canonical(table, start, reflect=True)[0]):
            matches.append(record)
    result = {'commit': commit, 'scope': SCOPE, 'all_tm_paths': len(current),
              'missing_paths': missing, 'nonparseable': bad,
              'working_state_count_histogram': dict(sorted(state_counts.items())),
              'literal_215_tables': len(tables), 'distinct_rooted_graphs': len(signatures),
              'matches_including_global_reflection': matches,
              'all_tm_inputs': all_inputs, 'tables': tables}
    assert not missing and not bad and not matches
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('all_tm_inputs', 'tables')}, indent=2))


if __name__ == '__main__':
    main()
