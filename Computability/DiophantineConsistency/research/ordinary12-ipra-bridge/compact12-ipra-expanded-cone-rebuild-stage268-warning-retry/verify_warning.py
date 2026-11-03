#!/usr/bin/env python3
"""Match the fourteen pinned ModelCodedDecoderAccepted254 warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ModelCodedDecoderAccepted254.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage267/observations/batch-054/stage-0268/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '8dc35524b4bee93514673da1ea658a804f78ff5b16ea8cdfbf6e0a461fbebb0e'
REJECTED_SHA = '00bff6d23e5785a9c66b1a234a64b56dd682d0e0f3eda3e4daefa2b2ed97c016'
EXPECTED_SHA = 'af050e63c91d13e3e7983dd1d41541a2bd07d5f85f7bfafc2b9d6fefbea233d0'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 14:
        raise RuntimeError('warnings must name the expected source exactly fourteen times')
    return text.replace(source, '<SOURCE>')

def main():
    if len(sys.argv) != 2:
        raise RuntimeError('expected one retry compiler log')
    if sha(SOURCE) != SOURCE_SHA or sha(REJECTED) != REJECTED_SHA or sha(EXPECTED) != EXPECTED_SHA:
        raise RuntimeError('warning baseline source, rejected log or expected text drift')
    expected = EXPECTED.read_text()
    if normalized(REJECTED) != expected or normalized(Path(sys.argv[1])) != expected:
        raise RuntimeError('retry log differs from the independently normalized full log')
    if expected.count('warning:') != 14 or 'error:' in expected or 'sorryAx' in expected:
        raise RuntimeError('baseline does not contain exactly fourteen warnings')
    print('PASS the exact source-pinned fourteen exact linter warnings')

if __name__ == '__main__':
    main()
