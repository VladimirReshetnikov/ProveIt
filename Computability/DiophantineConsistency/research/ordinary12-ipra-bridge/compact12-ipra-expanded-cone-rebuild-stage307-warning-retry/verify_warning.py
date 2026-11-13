#!/usr/bin/env python3
"""Match one pinned LMatch warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LMatch.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage307/observations/batch-062/stage-0307/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '1e0712e98297ea9a6bfa2d73649f9fb92e4020345c2abcf2eb9db8c9a3f218df'
REJECTED_SHA = '592bf9992fb40d541bcbbac519cb5ed341f4d8d9dc7b925f05b7d2a6ef18218b'
EXPECTED_SHA = '58fc10967fd146ce94d7feb1082593d2caf3590b7e40f8272573d57501fe7399'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 1:
        raise RuntimeError('warnings must name the expected source exactly once')
    return text.replace(source, '<SOURCE>')

def main():
    if len(sys.argv) != 2:
        raise RuntimeError('expected one retry compiler log')
    if sha(SOURCE) != SOURCE_SHA or sha(REJECTED) != REJECTED_SHA or sha(EXPECTED) != EXPECTED_SHA:
        raise RuntimeError('warning baseline source, rejected log or expected text drift')
    expected = EXPECTED.read_text()
    if normalized(REJECTED) != expected or normalized(Path(sys.argv[1])) != expected:
        raise RuntimeError('retry log differs from the independently normalized full log')
    if expected.count('warning:') != 1 or 'error:' in expected or 'sorryAx' in expected:
        raise RuntimeError('baseline does not contain exactly one warning')
    print('PASS the exact one source-pinned warning')

if __name__ == '__main__':
    main()
