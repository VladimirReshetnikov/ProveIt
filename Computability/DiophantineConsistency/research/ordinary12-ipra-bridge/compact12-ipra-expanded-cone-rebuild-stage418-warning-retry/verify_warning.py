#!/usr/bin/env python3
"""Match 6 pinned QSchemaSem warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/QSchemaSem.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage415/observations/batch-084/stage-0418/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '2bdd4d88873db9d834b03e14cfc2596ce85cc75eab44734716a60d4092b5bd51'
REJECTED_SHA = '712c6ca9127aff8879724232a5d9492bc1b7c4fbc621b3c15a4252dbfdb591bf'
EXPECTED_SHA = '685b3a91d1170abd6b5cc38ed93b59402d0d6e69265f776b5ec318f6183db0ef'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 6:
        raise RuntimeError('warnings must name the expected source exactly 6 times')
    return text.replace(source, '<SOURCE>')

def main():
    if len(sys.argv) != 2:
        raise RuntimeError('expected one retry compiler log')
    if sha(SOURCE) != SOURCE_SHA or sha(REJECTED) != REJECTED_SHA or sha(EXPECTED) != EXPECTED_SHA:
        raise RuntimeError('warning baseline source, rejected log or expected text drift')
    expected = EXPECTED.read_text()
    if normalized(REJECTED) != expected or normalized(Path(sys.argv[1])) != expected:
        raise RuntimeError('retry log differs from the independently normalized full log')
    if expected.count('warning:') != 6 or 'error:' in expected or 'sorryAx' in expected:
        raise RuntimeError('baseline does not contain exactly 6 warnings')
    print('PASS the exact 6 source-pinned warnings')

if __name__ == '__main__':
    main()
