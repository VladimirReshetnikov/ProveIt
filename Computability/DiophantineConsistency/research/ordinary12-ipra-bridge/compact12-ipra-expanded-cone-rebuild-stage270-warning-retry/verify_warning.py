#!/usr/bin/env python3
"""Match the one pinned NativeTheory warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeTheory.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage269/observations/batch-054/stage-0270/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = 'f5a04f53a579d497ce3be3368f4ff377425a96edde3e33ab493ef800e3305966'
REJECTED_SHA = 'd810ac2f4b56d1383cf8a689dccc0b41187992625598078d7984ae52fa31140d'
EXPECTED_SHA = 'c02c9690e3e5fc45eaaddc4d9377f48067984adc34188db64a4990cb80c354b7'

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
    print('PASS the exact source-pinned one exact linter warning')

if __name__ == '__main__':
    main()
