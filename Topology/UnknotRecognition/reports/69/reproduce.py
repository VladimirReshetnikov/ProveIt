#!/usr/bin/env python3
"""Verify and assemble the delivered source subset, then reproduce one task."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def verify_sources():
    manifest = json.loads((ROOT/'PROVENANCE.json').read_text())
    for record in manifest['delivered_sources']:
        path = ROOT/record['path']
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != record['sha256']:
            raise ValueError('source hash mismatch: '+record['path'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--task', choices=('tests','algebra','example','audit','benchmark','replay','all'), default='tests')
    parser.add_argument('--work-dir', type=Path)
    parser.add_argument('--regina', action='store_true')
    parser.add_argument('--regina-path', type=Path)
    args = parser.parse_args()
    verify_sources()
    if args.work_dir:
        destination = args.work_dir.resolve()
        if destination.exists():
            raise ValueError('--work-dir must be a new directory')
        destination.mkdir(parents=True)
    else:
        destination = Path(tempfile.mkdtemp(prefix='proveit-support-reproduction-'))
    fast = destination/'fast'
    shutil.copytree(ROOT/'reference_snapshot'/'fast', fast)
    shutil.copytree(ROOT/'repo_overlay'/'Topology'/'UnknotRecognition'/'fast', fast, dirs_exist_ok=True)
    output = fast/'support_research'/'results_local'
    output.mkdir()
    print('Verified source assembled at:', destination, flush=True)
    dependency = []
    environment = os.environ.copy()
    if args.regina_path:
        dependency = ['--regina-path', str(args.regina_path.resolve())]
        environment['PYTHONPATH'] = str(args.regina_path.resolve()) + os.pathsep + environment.get('PYTHONPATH', '')
    tasks = ['tests','algebra','example','audit','replay','benchmark'] if args.task == 'all' else [args.task]
    reports = []
    for task in tasks:
        if task == 'tests':
            commands = [['support_research/run_tests.py', *dependency, '--output', str(output/'regression.json')]]
        elif task == 'algebra':
            commands = [['support_research/audit_extra.py'], ['support_research/audit_focus.py']]
        elif task == 'example':
            commands = [['support_research/example.py']]
        elif task == 'audit':
            commands = [['support_research/audit.py', *dependency, '--output', str(output/'audit.json')]]
            if args.regina:
                commands[0].append('--regina')
        elif task == 'replay':
            commands = [['support_research/replay_evidence.py', '--output', str(output/'evidence_replay.json')]]
        else:
            commands = [['support_research/benchmark.py', '--diagrams', '1,4,8,16,32', '--output', str(output/'benchmark.json')]]
        for index, command in enumerate(commands):
            log = output/f'{task}-{index}.log'
            print('Running:', ' '.join(command), flush=True)
            with log.open('w') as stream:
                result = subprocess.run([sys.executable, *command], cwd=fast,
                                        env=environment, stdout=stream, stderr=subprocess.STDOUT)
            reports.append(dict(task=task, command=command, exit_code=result.returncode, log=str(log)))
            print(log.read_text(), end='', flush=True)
            if result.returncode:
                (destination/'reproduction_result.json').write_text(json.dumps(reports, indent=2)+'\n')
                return result.returncode
    (destination/'reproduction_result.json').write_text(json.dumps(reports, indent=2)+'\n')
    print('All requested tasks passed. Results:', output)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
