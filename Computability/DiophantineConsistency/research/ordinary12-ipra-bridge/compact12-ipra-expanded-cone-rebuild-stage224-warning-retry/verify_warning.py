#!/usr/bin/env python3
"""Match the two pinned KLowerQHyp warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerQHyp.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage223-retry/observations/batch-045/stage-0224/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '342485cb6294e12d0c52cc747758d447221670ce7dfda096b2f242d7a2974e62'
REJECTED_SHA = '119d46f5ec116c6f36cfd69045c6489a0cec956e8d8a0a6dcbb6f7ca682638f5'
EXPECTED_SHA = '8ca0f9a532f94049c3016af5efdfdec0e2ff3c3457f6c0c56efd0d69a65108b0'

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
    print('PASS the exact source-pinned unused-variable warnings')

if __name__ == '__main__':
    main()
