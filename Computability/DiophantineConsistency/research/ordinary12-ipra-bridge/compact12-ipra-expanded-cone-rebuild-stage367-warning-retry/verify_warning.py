#!/usr/bin/env python3
"""Match 3 pinned R2Quant warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Quant.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage357/observations/batch-074/stage-0367/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '1220da7c83aa7d86de81805fd26035ffee7bf9c8cc6eef08c98e30a6b6c7e66b'
REJECTED_SHA = '65911551b9827db3ac848194ab2436931830c1ea98daa8a018304c535e5a58c6'
EXPECTED_SHA = '2c0502cc2cc152ebddcecea78fbcf28f6c866e5bf86461541429e578ae4fea5f'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 3:
        raise RuntimeError('warnings must name the expected source exactly 3 times')
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
        raise RuntimeError('baseline does not contain exactly 3 warnings')
    print('PASS the exact 3 source-pinned warnings')

if __name__ == '__main__':
    main()
