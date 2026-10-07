#!/usr/bin/env python3
"""Read-only Report297 checks using the unchanged independently audited classifier."""
import sys
sys.dont_write_bytecode = True
import importlib.util
from math import isqrt
from pathlib import Path

HERE = Path(__file__).absolute().parent


def main():
    if len(sys.argv) != 1:
        raise ValueError('this read-only check accepts no arguments; use classify.py for explicit regeneration')
    spec = importlib.util.spec_from_file_location('finite_saturation_classifier', HERE / 'classify.py')
    classifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(classifier)
    sys.argv = [str(HERE / 'classify.py'), '--verify', str(HERE)]
    classifier.main()
    possible_inner = [q for q in classifier.MAXIMA if (q-1) % 3 == 0
                      and isqrt((q-1)//3)**2 == (q-1)//3]
    classifier.require(possible_inner == [4, 13], 'inner rational support candidates differ')
    possible_outer = [q for q in possible_inner
                     if isqrt(q*isqrt((q-1)//3)-(q-1))**2 == q*isqrt((q-1)//3)-(q-1)]
    classifier.require(possible_outer == [4] and classifier.MAXIMA[4] == 1,
                       'rational equality order differs')
    classifier.require(classifier.W(27, 3)-classifier.W(27, 2) == 10582,
                       'order 27 displayed gap differs')
    classifier.require(classifier.W(81, 7)-classifier.W(81, 8) == 13515678,
                       'order 81 displayed gap differs')
    print('PASS: rational support order and indicator attainment only at order/index 4 among n>=3.')
    print('PASS: exact displayed comparison gaps at orders 27 and 81.')


if __name__ == '__main__':
    main()
