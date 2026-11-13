#!/usr/bin/env python3
"""Match 6 pinned LGlue3 warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LGlue3.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage312/observations/batch-063/stage-0312/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '9f35461486789868b658e45134731f8a32a36026d0a91916ec288f7b9401dbaf'
REJECTED_SHA = '19b2422b522caaf7827b0819716ab28a89980df0da53f46180fd8cebfb885ee2'
EXPECTED_SHA = '19a642ca393e6836a231c71931ca292cc7d4c26f758c35774142409520407b44'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 6:
        raise RuntimeError('warnings must name the expected source exactly 6 times')
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
        raise RuntimeError('baseline does not contain exactly 6 warnings')
    print('PASS the exact 6 source-pinned warnings')

if __name__ == '__main__':
    main()
