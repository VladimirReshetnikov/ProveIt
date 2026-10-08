#!/usr/bin/env python3
"""Apply each integration patch to a fresh reference and compare every source byte."""
import hashlib
import json
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


def inventory(directory):
    return {str(path.relative_to(directory)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(directory.rglob('*'))
            if path.is_file() and '__pycache__' not in path.parts and path.suffix != '.pyc'}


def main():
    expected = inventory(ROOT / 'fast')
    results = []
    for filename, reference in REFERENCES.items():
        with tempfile.TemporaryDirectory(prefix='unknot-apply-') as directory:
            directory = Path(directory)
            target = directory / TARGET
            target.parent.mkdir(parents=True)
            shutil.copytree(ROOT / 'reference' / reference, target,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            subprocess.run(['git', 'init', '-q', str(directory)], check=True)
            patch = ROOT / 'integration' / filename
            for arguments in [['--check'], []]:
                subprocess.run(['git', '-C', str(directory), 'apply', *arguments, str(patch)],
                               check=True, capture_output=True)
            actual = inventory(target)
            if actual != expected:
                missing = sorted(set(expected) - set(actual))
                extra = sorted(set(actual) - set(expected))
                changed = sorted(name for name in expected.keys() & actual.keys()
                                 if expected[name] != actual[name])
                raise ValueError(f'{filename}: missing={missing}, extra={extra}, changed={changed}')
            results.append({'patch': filename, 'reference': reference,
                            'patch_sha256': hashlib.sha256(patch.read_bytes()).hexdigest(),
                            'source_files_compared': len(expected), 'status': 'passed'})
    output = {'target': str(TARGET), 'checks': results,
              'verification': 'git apply --check; git apply; complete SHA-256 inventory equality'}
    (ROOT / 'provenance').mkdir(exist_ok=True)
    (ROOT / 'provenance' / 'integration_verification.json').write_text(
        json.dumps(output, indent=2) + '\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
