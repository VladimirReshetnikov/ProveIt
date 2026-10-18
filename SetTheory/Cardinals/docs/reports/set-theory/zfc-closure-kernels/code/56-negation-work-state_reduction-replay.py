#!/usr/bin/env python3
"""Run an archived experiment in a fresh directory against a local checkout.

Original evidence scripts remain byte-for-byte unchanged. Staged copies of
scripts with a session-specific BASE path receive only a path-literal update;
the before/after hashes and replacement are recorded in relocation.json.
There is no network access and no repository mutation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
OLD_BASE = '/workspace/scratch/bf00ce1dffdf/source/ProveIt/Computability/BusyBeaver/Research/ZFC'
FOLDS = ['gap_fold_search.py', 'action_fold_search.py', 'phase_action_fold_search.py',
         'quotient_action_fold_search.py', 'ranked_fold_search.py']
SCRIPTS = FOLDS + ['two_action_search.py', 'box_mixed_search.py',
                  'box_mixed_affine.py', 'box_mixed_gap_affine.py', 'audit_ranked_contract.py']


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--work', type=Path, required=True)
    ap.add_argument('--script', choices=SCRIPTS, required=True)
    ap.add_argument('arguments', nargs=argparse.REMAINDER)
    args = ap.parse_args()
    repo, work = args.repo.resolve(), args.work.resolve()
    if work == repo or repo in work.parents or work == HERE or HERE in work.parents:
        ap.error('Use a fresh external work directory outside the repository and evidence directory.')
    work.mkdir(parents=True, exist_ok=True)
    # Preserve enough path depth for the archived ROOT default; folds receive
    # an explicit --repo argument, so that default is never used.
    stage = work / 'staged' / 'tools' / 'search' / 'drivers'
    stage.mkdir(parents=True, exist_ok=False)
    new_base = str(repo / 'Computability/BusyBeaver/Research/ZFC')
    records = []
    for source in sorted(HERE.glob('*.py')):
        raw = source.read_bytes()
        text = raw.decode()
        changes = text.count(repr(OLD_BASE))
        assert changes in (0, 1)
        changed = text.replace(repr(OLD_BASE), repr(new_base)).encode()
        (stage / source.name).write_bytes(changed)
        records.append(dict(file=source.name, original_sha256=sha(raw),
                            configured_sha256=sha(changed), path_literal_replacements=changes))
    for relative in ['box_mixed_results.json', 'ranked_fold_scratch/ranked_action_quotient.json']:
        src, dest = HERE / relative, stage / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, dest)
    extra = args.arguments
    if extra and extra[0] == '--':
        extra = extra[1:]
    command = [sys.executable, '-B', str(stage / args.script)]
    if args.script in FOLDS:
        command += ['--repo', str(repo), '--scratch', str(work / 'affine'),
                    '--output', str(work / 'result.json')]
    if args.script == 'box_mixed_search.py':
        command += ['--output', str(stage / 'box_mixed_results.json')]
    command += extra
    record = dict(scope=__doc__, repo=str(repo), work=str(work), stage=str(stage),
                  base_path_replacement=dict(before=OLD_BASE, after=new_base),
                  files=records, command=command)
    (work / 'relocation.json').write_text(json.dumps(record, indent=2) + '\n')
    completed = subprocess.run(command, cwd=work)
    raise SystemExit(completed.returncode)


if __name__ == '__main__':
    main()
