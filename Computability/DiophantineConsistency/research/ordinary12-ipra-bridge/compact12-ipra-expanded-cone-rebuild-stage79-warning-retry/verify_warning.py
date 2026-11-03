#!/usr/bin/env python3
"""Independently match the single pinned KLowerRaw warning, after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerRaw.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage77/observations/batch-016/stage-0079/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '9c4d606be83bdb5da13115f7bbe05b84c8aee1a1f5a2b85518fa6dd4327ec5b7'
REJECTED_SHA = '8200afd8ab177e93863b2e2f9deef49bfa79049b29d8d57a7bce2f60ce89aefa'
EXPECTED_SHA = '99e2bfd537967357a084cd466ee67eaad26a8892b135d9b66dd1c591e0a81f00'

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
        raise RuntimeError('the retry log differs from the independently normalized warning')
    if expected.count('warning:') != 1 or 'error:' in expected or 'sorryAx' in expected:
        raise RuntimeError('baseline is not exactly one warning')
    print('PASS one exact source-pinned, normalized unused-section-variable warning')

if __name__ == '__main__':
    main()
