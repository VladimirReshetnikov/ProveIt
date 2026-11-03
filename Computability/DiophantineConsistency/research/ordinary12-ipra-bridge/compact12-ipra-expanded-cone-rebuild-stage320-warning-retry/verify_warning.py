#!/usr/bin/env python3
"""Match 1 pinned SeedTemplate222 warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/SeedTemplate222.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage318/observations/batch-064/stage-0320/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = 'b04134d2874e123226706faa519154a0ec76055a5cb89f04eeead75be368e6bf'
REJECTED_SHA = 'e787a3b26247404a26393a23b7b5ea88ed1f261dcefa758c3a9bedc4278ddb0b'
EXPECTED_SHA = 'c7095d0df40a8db77400b7ef35ef0346c856ac040aef77ebb4c651d04b3e36d3'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 1:
        raise RuntimeError('warnings must name the expected source exactly 1 times')
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
        raise RuntimeError('baseline does not contain exactly 1 warnings')
    print('PASS the exact 1 source-pinned warnings')

if __name__ == '__main__':
    main()
