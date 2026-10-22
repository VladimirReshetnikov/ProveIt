#!/usr/bin/env python3
"""Check the four proposed patches together without changing the checkout.

Copies only pinned patch targets and required producer inputs to a temporary
directory, checks/applies each patch there, and replays the affected producers.
Requires Python 3.10+ and Git; no proof assistant or network is needed.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
BASE = Path('Computability/BusyBeaver/Research/ZFC/k225-formal')
LEAN = Path('Computability/BusyBeaver/Lean')


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_hash(path: Path) -> str | None:
    return sha(path.read_bytes()) if path.exists() else None


def safe_relative(name: str) -> Path:
    rel = PurePosixPath(name)
    if rel.is_absolute() or '..' in rel.parts or not rel.parts:
        raise RuntimeError('Unsafe relative path: ' + name)
    return Path(*rel.parts)


def main() -> None:
    if not __debug__:
        raise RuntimeError('Run ordinary Python without -O')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True,
                        help='Read-only baseline ProveIt checkout at the pinned commit')
    parser.add_argument('--patches', type=Path, required=True,
                        help='Directory containing the four numbered patches')
    parser.add_argument('--out', type=Path, required=True,
                        help='New evidence directory outside the baseline checkout')
    args = parser.parse_args()
    repo, patches, out = args.repo.resolve(), args.patches.resolve(), args.out.resolve()
    if out.is_relative_to(repo):
        raise RuntimeError('--out must be outside the read-only checkout')
    if out.exists():
        raise RuntimeError('--out must not exist: ' + str(out))
    manifest_bytes = (HERE / 'integration_manifest.json').read_bytes()
    manifest = json.loads(manifest_bytes)
    helper = HERE / 'check_rocq_producer.py'
    if file_hash(helper) != manifest['rocq_producer_helper_sha256']:
        raise RuntimeError('Rocq producer checker hash mismatch')
    env = dict(os.environ)
    # Git is used only to read HEAD in the real checkout and to apply patches in
    # a fresh standalone temporary directory. Discard external repository hints.
    for name in ('GIT_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE', 'GIT_COMMON_DIR',
                 'PYTHONOPTIMIZE', 'PYTHONPATH'):
        env.pop(name, None)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    rev = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=repo, env=env,
                         capture_output=True, text=True, check=True).stdout.strip()
    if rev != manifest['base_commit']:
        raise RuntimeError('Wrong baseline revision: ' + rev)
    for item in manifest['baseline_files']:
        path = repo / safe_relative(item['path'])
        if file_hash(path) != item['sha256']:
            raise RuntimeError('Baseline source changed: ' + item['path'])
    for stage in manifest['patch_order']:
        path = patches / safe_relative(stage['filename'])
        if file_hash(path) != stage['patch_sha256']:
            raise RuntimeError('Patch hash mismatch: ' + stage['filename'])
        targets = re.findall(r'^\+\+\+ b/(.+)$', path.read_text(), re.M)
        if set(targets) != {r['path'] for r in stage['changes']}:
            raise RuntimeError('Patch targets differ from manifest: ' + stage['filename'])
    out.mkdir(parents=True)
    (out / 'logs').mkdir()
    receipt = {
        'schema_version': 1,
        'base_commit': rev,
        'scope': manifest['scope'],
        'checker_sha256': sha(Path(__file__).read_bytes()),
        'manifest_sha256': sha(manifest_bytes),
        'rocq_producer_helper_sha256': file_hash(helper),
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'status': 'running',
        'baseline_paths_checked': len(manifest['baseline_files']),
        'baseline_files_copied': sum(r['sha256'] is not None
                                     for r in manifest['baseline_files']),
        'operations': [],
        'patches': [],
        'checked_component_source_matches': [],
        'producer_checks': [],
    }

    def save() -> None:
        (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')

    save()
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix='k215-patch-check-') as tmp:
        temporary = Path(tmp)
        staging = temporary / 'staging'
        staging.mkdir()
        work = temporary / 'producer-work'
        work.mkdir()
        substitutions = sorted([(str(staging), 'STAGING'), (str(temporary), 'TEMP'),
                                (str(repo), 'REPO'), (str(patches), 'PATCHES'),
                                (str(HERE), 'CHECKER')], key=lambda x: len(x[0]), reverse=True)

        def portable(text: str) -> str:
            for old, new in substitutions:
                text = text.replace(old, new)
            return text

        def run(label: str, command: list[str], cwd: Path) -> None:
            begin = time.monotonic()
            result = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True)
            output = portable(result.stdout + result.stderr)
            log = Path('logs') / (label + '.log')
            (out / log).write_text(output)
            receipt['operations'].append({
                'label': label, 'command': [portable(x) for x in command],
                'cwd': portable(str(cwd)), 'exit_code': result.returncode,
                'seconds': time.monotonic() - begin,
                'log': log.as_posix(), 'log_sha256': sha(output.encode()),
                'temporary_paths_normalized': True,
            })
            save()
            if result.returncode:
                receipt['status'] = 'failed'
                receipt['failed_operation'] = label
                save()
                raise RuntimeError(label + ' failed; see ' + str(out / log))

        for item in manifest['baseline_files']:
            if item['sha256'] is not None:
                rel = safe_relative(item['path'])
                target = staging / rel
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((repo / rel).read_bytes())
        for index, stage in enumerate(manifest['patch_order'], 1):
            name = stage['filename']
            for item in stage['changes']:
                if file_hash(staging / safe_relative(item['path'])) != item['before_sha256']:
                    raise RuntimeError('Wrong intermediate source before ' + name + ': ' + item['path'])
            patch = patches / name
            run(f'{index:02d}_apply_check', ['git', 'apply', '--check', str(patch)], staging)
            run(f'{index:02d}_apply', ['git', 'apply', str(patch)], staging)
            for item in stage['changes']:
                if file_hash(staging / safe_relative(item['path'])) != item['after_sha256']:
                    raise RuntimeError('Applied source mismatch after ' + name + ': ' + item['path'])
            receipt['patches'].append({'filename': name, 'patch_sha256': stage['patch_sha256'],
                                       'changed_paths': len(stage['changes']),
                                       'apply_check_passed': True, 'applied': True,
                                       'all_output_hashes_match': True})
            save()
            print('PASS:', name, flush=True)
        for item in manifest['checked_component_source_matches']:
            actual = file_hash(staging / safe_relative(item['path']))
            if actual != item['source_sha256']:
                raise RuntimeError('Checked component mismatch: ' + item['path'])
            receipt['checked_component_source_matches'].append(dict(item, byte_equal=True))
        # Maintained Lean producer: pins its own inputs and compares all three
        # generated outputs against the applied Lean source tree.
        run('lean_shared_basis_producer', [sys.executable, '-B',
            str(staging / BASE / 'generate_dominated_implication_lean.py'),
            '--out', str(staging / LEAN), '--check'], staging)
        receipt['producer_checks'].append({'producer': 'Lean shared implication basis',
                                           'outputs_byte_equal': 3, 'status': 'passed'})
        fork = work / 'lean-forks'
        fork_sources = fork / 'BusyBeaver/ZFC'
        fork_sources.mkdir(parents=True)
        (fork_sources / 'Enum254.lean').write_bytes(
            (staging / LEAN / 'BusyBeaver/ZFC/Enum254.lean').read_bytes())
        for filename, module in [('generate_enum222.py', 'Enum222'),
                                 ('generate_enumdom.py', 'EnumDom')]:
            run('lean_' + module + '_producer',
                [sys.executable, '-B', str(staging / BASE / filename)], fork)
            actual = (fork_sources / (module + '.lean')).read_bytes()
            expected = (staging / LEAN / 'BusyBeaver/ZFC' / (module + '.lean')).read_bytes()
            if actual != expected:
                raise RuntimeError('Enumerator fork producer mismatch: ' + module)
            receipt['producer_checks'].append({'producer': filename, 'module': module,
                                               'source_sha256': sha(actual),
                                               'byte_equal': True, 'status': 'passed'})
        rocq_out = work / 'rocq-producer'
        run('rocq_calculus_producer', [sys.executable, '-B', str(helper),
            '--repo', str(staging), '--out', str(rocq_out)], staging)
        producer_receipt = json.loads(portable((rocq_out / 'receipt.json').read_text()))
        (out / 'rocq_producer_receipt.json').write_text(
            json.dumps(producer_receipt, indent=2) + '\n')
        if producer_receipt['status'] != 'PASS':
            raise RuntimeError('Rocq producer comparison failed')
        receipt['producer_checks'].append({'producer': 'patched regenerate215.calculus_files',
                                           'outputs_byte_equal': len(producer_receipt['comparisons']),
                                           'status': 'passed',
                                           'scope': producer_receipt['scope']})
        # Prove the actual checkout's relevant files remained byte-identical.
        for item in manifest['baseline_files']:
            if file_hash(repo / safe_relative(item['path'])) != item['sha256']:
                raise RuntimeError('Baseline changed during check: ' + item['path'])
        receipt['original_checkout_source_pins_unchanged'] = True
        receipt['temporary_staging_removed_on_exit'] = True
        receipt['status'] = 'passed'
        receipt['elapsed_seconds'] = time.monotonic() - started
        receipt['completed_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    print('PASS: four ordered patches, 13 checked component sources, and all affected producers.')


if __name__ == '__main__':
    main()
