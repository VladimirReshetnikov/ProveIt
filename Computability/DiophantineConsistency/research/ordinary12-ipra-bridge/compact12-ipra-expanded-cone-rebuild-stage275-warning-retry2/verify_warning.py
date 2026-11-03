#!/usr/bin/env python3
"""Match the four pinned NativeInterp warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeSchemaSem.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage273/observations/batch-055/stage-0275/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '8e66976b169584af3883c1636b64b7baa51395397290d8a1458d315a2ac972fd'
REJECTED_SHA = '3bfb896c2aad415bc0bfcc0ad90705e28e4a16788f33d2b31b7e7973ef44cddb'
EXPECTED_SHA = '72c3c834f884ee3d444c96f9db8d23779f3ffdbcc1fab4a329a7211c040ea88d'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 6:
        raise RuntimeError('warnings must name the expected source exactly six times')
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
        raise RuntimeError('baseline does not contain exactly six warnings')
    print('PASS the exact source-pinned six exact linter warnings')

if __name__ == '__main__':
    main()
