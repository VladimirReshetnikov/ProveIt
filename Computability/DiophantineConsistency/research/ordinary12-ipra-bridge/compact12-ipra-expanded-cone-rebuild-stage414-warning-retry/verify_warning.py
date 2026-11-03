#!/usr/bin/env python3
"""Match 4 pinned QInterp warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/QInterp.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage402/observations/batch-083/stage-0414/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = 'b52a4c456a852af54336afba2bcf61874866644b8f4355478a53f8fa1c8c590e'
REJECTED_SHA = 'd8fa78030a6cbc3a56b34e9f0e2247d44d53a35c51799d3a4904fd8ab1bf0f98'
EXPECTED_SHA = 'beb1e698c8e3c77b2955fb918d7823a01c3063b133e9a9bccdf0e216f22723aa'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 4:
        raise RuntimeError('warnings must name the expected source exactly 4 times')
    return text.replace(source, '<SOURCE>')

def main():
    if len(sys.argv) != 2:
        raise RuntimeError('expected one retry compiler log')
    if sha(SOURCE) != SOURCE_SHA or sha(REJECTED) != REJECTED_SHA or sha(EXPECTED) != EXPECTED_SHA:
        raise RuntimeError('warning baseline source, rejected log or expected text drift')
    expected = EXPECTED.read_text()
    if normalized(REJECTED) != expected or normalized(Path(sys.argv[1])) != expected:
        raise RuntimeError('retry log differs from the independently normalized full log')
    if expected.count('warning:') != 4 or 'error:' in expected or 'sorryAx' in expected:
        raise RuntimeError('baseline does not contain exactly 4 warnings')
    print('PASS the exact 4 source-pinned warnings')

if __name__ == '__main__':
    main()
