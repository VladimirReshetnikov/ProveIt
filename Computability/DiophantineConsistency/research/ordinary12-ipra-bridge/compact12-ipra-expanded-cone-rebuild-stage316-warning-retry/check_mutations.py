#!/usr/bin/env python3
"""Check that the exact warning verifier rejects mutated logs."""
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ORIGINAL = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage315/observations/batch-064/stage-0316/compile.log'

def main():
    text = ORIGINAL.read_text()
    cases = {'extra-warning': text + 'warning: extra\n',
             'added-error': text + 'error: extra\n',
             'added-sorry': text + 'sorryAx\n',
             'missing-warning': text.replace('warning:', 'notice:', 1),
             'wrong-warning': text.replace('warning:', 'changed-warning:', 1)}
    if any(value == text for value in cases.values()):
        raise RuntimeError('mutation did not change source log')
    with tempfile.TemporaryDirectory(prefix='warning-baseline-negative-') as directory:
        for name, value in cases.items():
            path = Path(directory) / name
            path.write_text(value)
            proc = subprocess.run([sys.executable, '-I', '-B', str(HERE / 'verify_warning.py'), str(path)],
                                  capture_output=True, text=True)
            if proc.returncode == 0:
                raise RuntimeError(f'verifier accepted mutated log: {name}')
            print(f'{name}: rejected')

if __name__ == '__main__':
    main()
