#!/usr/bin/env python3
"""Match the four pinned NativeInterp warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeInterp.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage271/observations/batch-055/stage-0272/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '490fc7a2d9acc92b5a6b27663e577eaf328c57ed74fb1353e4553b714155b224'
REJECTED_SHA = '1aac1708f3d503adf706b9f1ed4fd52d86af5cc135718ec72f2b0f07775c0d93'
EXPECTED_SHA = '5101c4dfb5bcce0b75c54a4aed364edfd4e36a792ec5e756e09179cc22c6b685'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 4:
        raise RuntimeError('warnings must name the expected source exactly four times')
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
        raise RuntimeError('baseline does not contain exactly four warnings')
    print('PASS the exact source-pinned four exact linter warnings')

if __name__ == '__main__':
    main()
