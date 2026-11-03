#!/usr/bin/env python3
"""Match the one pinned ModelCodedDecoderRho6_254 warning after path normalization."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ModelCodedDecoderRho6_254.lean'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage251/observations/batch-051/stage-0251/compile.log'
EXPECTED = HERE / 'expected-warning.txt'
SOURCE_SHA = 'e1c20c8e6fd34954be933250ff9e10dab7bf4f55e6edf4e8fcf217257da061b3'
REJECTED_SHA = '77ab18510309dba5dc5bdfb258ed6bff1988bbd625d8b49e86aa5013b9b3169e'
EXPECTED_SHA = '8ada12747e090fa5db22e1b507bc35b463d3247b03d418868a593128b191a32c'

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
    print('PASS the exact source-pinned unnecessary-simpa warnings')

if __name__ == '__main__':
    main()
