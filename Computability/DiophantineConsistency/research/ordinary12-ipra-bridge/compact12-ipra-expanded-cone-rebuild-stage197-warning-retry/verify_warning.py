#!/usr/bin/env python3
"""Match the single pinned KQ1Basic warning after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Basic.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage196/observations/batch-040/stage-0197/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = 'c6dcf8a8babed8e7544bc091a53070c923f67c97c2f3e8439783c243c8293ca8'
REJECTED_SHA = 'd36f414ca417b1858033e79a6d1c1f529c2c5f43ca3de9593125f94e5162b0d0'
EXPECTED_SHA = '7c0c01e0b041b48ea83b9e4fe5cad46ddbe2c03c542b34ce6107a5aa3c630145'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 1:
        raise RuntimeError('warning must name the expected source exactly once')
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
    print('PASS the exact source-pinned unused-variable warning')

if __name__ == '__main__':
    main()
