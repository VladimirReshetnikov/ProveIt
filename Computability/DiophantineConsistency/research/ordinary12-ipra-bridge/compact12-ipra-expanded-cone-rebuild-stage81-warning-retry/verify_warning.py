#!/usr/bin/env python3
"""Independently match the single pinned KLowerTag warning after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerTag.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage80/observations/batch-017/stage-0081/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = 'ef698a4b035fd93db09c51ff37c30d96ef3c5b944f8a75cd24168d12606461d3'
REJECTED_SHA = '3ae640bddbe65eb5e086ee5bce8bfdfcb978a60fe4580e042575ccb6bffa11ff'
EXPECTED_SHA = 'c8876f4a91179aaf43af11f90ca9d67d00491f874c2ded22706c2c4545e9bdfd'

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
        raise RuntimeError('retry log differs from the independently normalized warning')
    if expected.count('warning:') != 1 or 'error:' in expected or 'sorryAx' in expected:
        raise RuntimeError('baseline is not exactly one warning')
    print('PASS one exact source-pinned, normalized unused-section-variables warning')

if __name__ == '__main__':
    main()
