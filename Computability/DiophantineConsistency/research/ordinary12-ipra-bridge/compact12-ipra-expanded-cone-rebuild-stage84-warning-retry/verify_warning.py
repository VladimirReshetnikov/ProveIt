#!/usr/bin/env python3
"""Match the three pinned KQ1Model warnings and axiom reports after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Model.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage82/observations/batch-017/stage-0084/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '284f5c1a9ac828bd2b773fbfe365ec1d5b2471f7f6088e2b0f82abfc0fbfcd2a'
REJECTED_SHA = '00e83762778f03721393d83d3f971232944f39bab225ff080181cbac6c4d4f0a'
EXPECTED_SHA = 'ce41a6fcc3c0116286d878add6ddb33c1f9d39970c3d4285d71e77dcf08b9ddb'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 3:
        raise RuntimeError('log must name the expected source exactly three times')
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
    print('PASS the exact three source-pinned warnings and axiom-report lines')

if __name__ == '__main__':
    main()
