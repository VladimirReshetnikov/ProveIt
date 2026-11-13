#!/usr/bin/env python3
"""Match 6 pinned R2Gic warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Gic.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage369/observations/batch-074/stage-0369/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '7779d0b6834186b47068dcd74b0867e126f90df2eba4f46d98f826aef0a69a9f'
REJECTED_SHA = 'ba1e627ebdc967f17ba5645893e7623f6fac8aec5cc5e280f9353f19377267d3'
EXPECTED_SHA = 'a3b8a838ac1219f48e392d963c44e95db4e3c5810efae50c0df2653ca743fe48'

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
