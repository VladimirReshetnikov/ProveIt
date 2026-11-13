#!/usr/bin/env python3
"""Match seven pinned LDriverBase warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LDriverBase.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage301/observations/batch-061/stage-0301/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '071db8229f82d2d7340f7f7b69de503f7834d2c9fd5f7b890e702bcd80e1a255'
REJECTED_SHA = '7d126379f2b85f4843c3971bc1175d63f2dc8a46ec570d9e47f8429ed13b3f5f'
EXPECTED_SHA = 'b566b1b13506219eab779caa58a23953a27cc07159d002bce1b475be247861c8'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 7:
        raise RuntimeError('warnings must name the expected source exactly seven times')
    return text.replace(source, '<SOURCE>')

def main():
    if len(sys.argv) != 2:
        raise RuntimeError('expected one retry compiler log')
    if sha(SOURCE) != SOURCE_SHA or sha(REJECTED) != REJECTED_SHA or sha(EXPECTED) != EXPECTED_SHA:
        raise RuntimeError('warning baseline source, rejected log or expected text drift')
    expected = EXPECTED.read_text()
    if normalized(REJECTED) != expected or normalized(Path(sys.argv[1])) != expected:
        raise RuntimeError('retry log differs from the independently normalized full log')
    if expected.count('warning:') != 7 or 'error:' in expected or 'sorryAx' in expected:
        raise RuntimeError('baseline does not contain exactly seven warnings')
    print('PASS the exact seven source-pinned warnings')

if __name__ == '__main__':
    main()
