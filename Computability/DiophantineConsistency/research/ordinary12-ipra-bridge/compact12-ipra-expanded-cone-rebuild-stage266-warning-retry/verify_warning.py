#!/usr/bin/env python3
"""Match the eleven pinned ModelCodedDecoderCollection254 warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ModelCodedDecoderCollection254.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage264/observations/batch-054/stage-0266/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '563030a91b6943ecedad64e3d061b6efaf8fd9439ebe014de345ae5a12c5b2c4'
REJECTED_SHA = 'ff7b263bf54dedcc15db623c0869b157d34e33195faec3a8c0b0c9f57259f58b'
EXPECTED_SHA = '34b600113b35c63779639db4b80bb78b6027c160417fff80411fb2abb3a15f7c'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 11:
        raise RuntimeError('warnings must name the expected source exactly eleven times')
    return text.replace(source, '<SOURCE>')

def main():
    if len(sys.argv) != 2:
        raise RuntimeError('expected one retry compiler log')
    if sha(SOURCE) != SOURCE_SHA or sha(REJECTED) != REJECTED_SHA or sha(EXPECTED) != EXPECTED_SHA:
        raise RuntimeError('warning baseline source, rejected log or expected text drift')
    expected = EXPECTED.read_text()
    if normalized(REJECTED) != expected or normalized(Path(sys.argv[1])) != expected:
        raise RuntimeError('retry log differs from the independently normalized full log')
    if expected.count('warning:') != 11 or 'error:' in expected or 'sorryAx' in expected:
        raise RuntimeError('baseline does not contain exactly eleven warnings')
    print('PASS the exact source-pinned eleven exact linter warnings')

if __name__ == '__main__':
    main()
