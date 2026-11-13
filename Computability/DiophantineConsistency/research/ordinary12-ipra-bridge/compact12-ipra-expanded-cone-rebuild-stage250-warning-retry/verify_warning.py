#!/usr/bin/env python3
"""Match the three pinned ModelCodedDecoderRho4_254 warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ModelCodedDecoderRho4_254.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage240/observations/batch-050/stage-0250/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = 'e46032e3cee19b2ba97f6d8bf76547aa422cceee41759ddcd282dc419e90cc9d'
REJECTED_SHA = '0438b6c8cd26dbd24c5b9409df156fedf879cf9f92f5bad7d378640a3827ef58'
EXPECTED_SHA = '4907ef8efcf1fb484476b1ea67f1bdf595432f1b3df358ca7ee4a336395794f1'

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
    print('PASS the exact source-pinned unnecessary-simpa warnings')

if __name__ == '__main__':
    main()
