#!/usr/bin/env python3
"""Match 2 pinned SeedBundleTemplates222 warnings after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/SeedBundleTemplates222.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage321/observations/batch-065/stage-0321/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = '84f71512c01d16bd52d100afdbe757f6e1ea275b01f7319c49403b629f2fb40e'
REJECTED_SHA = 'db925c335ce79ed9eceef065778fa32c300b4af9a2f69e3e7f783fba68a8d4de'
EXPECTED_SHA = '69a959afd64df98351de3c2d628f4904815a75ed2829cd69a0d0466c92e892ae'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def normalized(path):
    text = path.read_text()
    source = str(SOURCE)
    if text.count(source) != 2:
        raise RuntimeError('warnings must name the expected source exactly 2 times')
    return text.replace(source, '<SOURCE>')

def main():
    if len(sys.argv) != 2:
        raise RuntimeError('expected one retry compiler log')
    if sha(SOURCE) != SOURCE_SHA or sha(REJECTED) != REJECTED_SHA or sha(EXPECTED) != EXPECTED_SHA:
        raise RuntimeError('warning baseline source, rejected log or expected text drift')
    expected = EXPECTED.read_text()
    if normalized(REJECTED) != expected or normalized(Path(sys.argv[1])) != expected:
        raise RuntimeError('retry log differs from the independently normalized full log')
    if expected.count('warning:') != 2 or 'error:' in expected or 'sorryAx' in expected:
        raise RuntimeError('baseline does not contain exactly 2 warnings')
    print('PASS the exact 2 source-pinned warnings')

if __name__ == '__main__':
    main()
