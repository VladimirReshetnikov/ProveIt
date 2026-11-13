#!/usr/bin/env python3
"""Match one pinned LFvBound warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LFvBound.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage302/observations/batch-062/stage-0306/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '786196f7968c41550a12ca2c1a80ce1cc7e096e70aa94f016b94d1d1e860b237'
REJECTED_SHA = 'fc480fef80f60323fd1b50a4d61c2b004d1e590c25b8455527d0b86a84a300a6'
EXPECTED_SHA = '058a4167adde870fdbacb865da687417046ac070c86a7bc7304bf550aecc9ac7'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 1:
        raise RuntimeError('warnings must name the expected source exactly once')
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
        raise RuntimeError('baseline does not contain exactly one warning')
    print('PASS the exact one source-pinned warning')

if __name__ == '__main__':
    main()
