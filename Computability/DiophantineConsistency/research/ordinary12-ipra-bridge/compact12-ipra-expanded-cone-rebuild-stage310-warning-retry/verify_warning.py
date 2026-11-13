#!/usr/bin/env python3
"""Match three pinned LGlue1 warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LGlue1.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage308/observations/batch-062/stage-0310/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = 'a29f07c4d478034239d45e1cf9e002aa12cea02fb399c637e72c0701d2e015ba'
REJECTED_SHA = '31ac86cc09d9b2376acd039c6dbc2819c3d67bdbb3efbbbdd7b66e7e4a8582ba'
EXPECTED_SHA = 'ad7050a6d57fa2d9b1846bd28e563f7fca2692fbd713b97f26236f58f78366e1'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 3:
        raise RuntimeError('warnings must name the expected source exactly three times')
    return text.replace(source, '<SOURCE>')

def main():
    if len(sys.argv) != 2:
        raise RuntimeError('expected one retry compiler log')
    if sha(SOURCE) != SOURCE_SHA or sha(REJECTED) != REJECTED_SHA or sha(EXPECTED) != EXPECTED_SHA:
        raise RuntimeError('warning baseline source, rejected log or expected text drift')
    expected = EXPECTED.read_text()
    if normalized(REJECTED) != expected or normalized(Path(sys.argv[1])) != expected:
        raise RuntimeError('retry log differs from the independently normalized full log')
    if expected.count('warning:') != 3 or 'error:' in expected or 'sorryAx' in expected:
        raise RuntimeError('baseline does not contain exactly three warnings')
    print('PASS the exact three source-pinned warnings')

if __name__ == '__main__':
    main()
