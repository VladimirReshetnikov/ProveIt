#!/usr/bin/env python3
"""Match 8 pinned LReplBase warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LReplBase.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage315/observations/batch-064/stage-0316/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '14c41ee24aa6be978eac4b22e342bc4d4946fb7cddc38a8e81e529dcbd1634e2'
REJECTED_SHA = '2fc433ab16cdab754d8386c6175396d1a8e2b17466d373513b03cbcb3359621f'
EXPECTED_SHA = '8564b0ee9aec933716b0c7ee784d2c23c7ae8762a74c41f41ecb4dcaa8f5e42e'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 8:
        raise RuntimeError('warnings must name the expected source exactly 8 times')
    return text.replace(source, '<SOURCE>')

def main():
    if len(sys.argv) != 2:
        raise RuntimeError('expected one retry compiler log')
    if sha(SOURCE) != SOURCE_SHA or sha(REJECTED) != REJECTED_SHA or sha(EXPECTED) != EXPECTED_SHA:
        raise RuntimeError('warning baseline source, rejected log or expected text drift')
    expected = EXPECTED.read_text()
    if normalized(REJECTED) != expected or normalized(Path(sys.argv[1])) != expected:
        raise RuntimeError('retry log differs from the independently normalized full log')
    if expected.count('warning:') != 8 or 'error:' in expected or 'sorryAx' in expected:
        raise RuntimeError('baseline does not contain exactly 8 warnings')
    print('PASS the exact 8 source-pinned warnings')

if __name__ == '__main__':
    main()
