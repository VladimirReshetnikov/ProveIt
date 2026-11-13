#!/usr/bin/env python3
"""Match 2 pinned R2Fixed warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Fixed.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage370/observations/batch-075/stage-0371/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '9d45176105a1587ef37d7cf31a4ae70a305c15f6469afc5765e82ba297353a64'
REJECTED_SHA = 'c0ee68210076c7dba9e3f4fb0effd07fe58aa200d2a9cc77d023c1c815571276'
EXPECTED_SHA = 'cbd0be31bdf54249af3cd2b66c45d0ed82b4e88e3d7fdd6fd50acdec6db2998a'

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
