#!/usr/bin/env python3
"""Match the two pinned ConstructibleInterpretation warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ConstructibleInterpretation.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage252/observations/batch-053/stage-0263/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = 'c6633453953825d6d9cd387bcbbffb839c4b61b10dc65a43ffd5bdc4dec4e04d'
REJECTED_SHA = '279a253b4aad516cb42e6a63a087c8d0155a222f02607d6b86f5815995a4366d'
EXPECTED_SHA = 'a0013896c8f1bd92a651342aa1f1d0c399097b72831a4731147699e81bbeaf71'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 2:
        raise RuntimeError('warnings must name the expected source exactly twice')
    return text.replace(source, '<SOURCE>')

def main():
    if len(sys.argv) != 2:
        raise RuntimeError('expected one retry compiler log')
    if sha(SOURCE) != SOURCE_SHA or sha(REJECTED) != REJECTED_SHA or sha(EXPECTED) != EXPECTED_SHA:
        raise RuntimeError('warning baseline source, rejected log or expected text drift')
    expected = EXPECTED.read_text()
    if normalized(REJECTED) != expected or normalized(Path(sys.argv[1])) != expected:
        raise RuntimeError('retry log differs from the independently normalized full log')
    if expected.count('warning:') != 2 or 'error:' in expected or 'sorryAx' in expected:
        raise RuntimeError('baseline does not contain exactly two warnings')
    print('PASS the exact source-pinned style and unused-instance warnings')

if __name__ == '__main__':
    main()
