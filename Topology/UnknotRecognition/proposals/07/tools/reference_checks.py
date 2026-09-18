"""Reproduce the independent dense checks of the two eleven-crossing fixtures."""
from __future__ import annotations
import json
import sys
import time
from common import ROOT, load
sys.path.insert(0, str(ROOT/'tests'))
from test_inherited import reference_reduced_rank
from fastunknot import alexander_polynomial
from fastunknot.simplify import legal_moves


def main() -> None:
    answers = {}
    for name in ('conway.json', 'kinoshita_terasaka.json'):
        diagram = load(name)
        start = time.perf_counter()
        rank = reference_reduced_rank(diagram)
        answers[name] = {
            'independent_dense_reduced_rank': rank,
            'seconds': time.perf_counter() - start,
            'alexander': alexander_polynomial(diagram),
            'legal_R1_R2': len(legal_moves(diagram)),
        }
        if rank != 33 or answers[name]['alexander'] != [1]:
            raise ArithmeticError(f'unexpected reference result for {name}: {answers[name]}')
    text = json.dumps(answers, indent=2)+'\n'
    (ROOT/'results/independent-dense-named.json').write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
