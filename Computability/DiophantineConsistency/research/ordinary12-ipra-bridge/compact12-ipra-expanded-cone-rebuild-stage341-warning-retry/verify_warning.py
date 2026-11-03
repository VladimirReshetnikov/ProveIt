#!/usr/bin/env python3
"""Match 1 pinned ValidatorEnvironmentAlpha254 warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEnvironmentAlpha254.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage338/observations/batch-069/stage-0341/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = 'a480a6db90cafe5fa1783e12991ca067948120cff79633e2b11568791d48c762'
REJECTED_SHA = 'd3a05920dcd46e15d63c67aa964c1b049d0c8e55c0ca9716fbcb7840fd9efd5b'
EXPECTED_SHA = '6736ec226d5a4658d04a5e754200fdb6c62fa65656af399d3ae215278605ae85'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 1:
        raise RuntimeError('warnings must name the expected source exactly 1 times')
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
        raise RuntimeError('baseline does not contain exactly 1 warnings')
    print('PASS the exact 1 source-pinned warnings')

if __name__ == '__main__':
    main()
