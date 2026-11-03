#!/usr/bin/env python3
"""Match 3 pinned LPeel warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LPeel.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage313/observations/batch-063/stage-0314/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '3b6161234776819955bc109d43fc3e3b2df96d267ed9e2ac3ba5e68fca1f4f78'
REJECTED_SHA = '5db5bd5ba54142edfb041c55ac6375a1646dc980e31732c55e9ebc8efb816257'
EXPECTED_SHA = '9209c94e607bf7566d7cf385cc7b8390daa22e082327d1541ca38daf51cb2f60'

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
