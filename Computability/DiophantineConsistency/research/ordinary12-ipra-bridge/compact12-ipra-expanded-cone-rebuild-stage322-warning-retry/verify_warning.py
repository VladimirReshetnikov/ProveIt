#!/usr/bin/env python3
"""Match 2 pinned ModelCodedDecoderBundle222 warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ModelCodedDecoderBundle222.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage322/observations/batch-065/stage-0322/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '05b0082ea467082b78c9021e1927c1b14fc99fd95a3746c8b00c0e764c8e3125'
REJECTED_SHA = '595451dfa180ef38bc4feb7837434c9c5c3373acc6893aba09ba4131b3cae023'
EXPECTED_SHA = 'a9dfcb65854e4296500443df81830bcb249a3baa94244122d55405612102b15a'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 2:
        raise RuntimeError('warnings must name the expected source exactly 2 times')
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
        raise RuntimeError('baseline does not contain exactly 2 warnings')
    print('PASS the exact 2 source-pinned warnings')

if __name__ == '__main__':
    main()
