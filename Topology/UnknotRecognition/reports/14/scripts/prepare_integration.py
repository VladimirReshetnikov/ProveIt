#!/usr/bin/env python3
"""Regenerate both integration patches from the included exact source snapshots."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TARGET = Path('Topology/UnknotRecognition/fast')
REFERENCES = {
    'from_repository.patch': 'repository-fast',
    'from_structural_0_3.patch': 'structural-fast',
}


def copy_source(source, target):
    shutil.copytree(source, target, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))


def run_git(directory, *arguments):
    return subprocess.run(['git', '-C', str(directory), *arguments], check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout


def main():
    (ROOT / 'integration').mkdir(exist_ok=True)
    for filename, reference in REFERENCES.items():
        with tempfile.TemporaryDirectory(prefix='unknot-patch-') as directory:
            directory = Path(directory)
            target = directory / TARGET
            target.parent.mkdir(parents=True)
            copy_source(ROOT / 'reference' / reference, target)
            run_git(directory, 'init', '-q')
            run_git(directory, 'add', '--all')
            run_git(directory, '-c', 'user.name=Artifact verification',
                    '-c', 'user.email=artifact@localhost', 'commit', '-q',
                    '-m', 'Reference snapshot')
            shutil.rmtree(target)
            copy_source(ROOT / 'fast', target)
            run_git(directory, 'add', '--all')
            patch = run_git(directory, 'diff', '--cached', '--binary', '--no-ext-diff')
            (ROOT / 'integration' / filename).write_bytes(patch)
            print(f'{filename}: {len(patch)} bytes')


if __name__ == '__main__':
    main()
