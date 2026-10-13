"""Compare the stable slope with the independently extracted E subcomplex.

The package-local ``fast`` directory is added to the import path automatically.
The default output is ``results/slope_audit.json`` in the package.
"""
from __future__ import annotations

import json
import sys
from collections import defaultdict
from itertools import product
from pathlib import Path
from random import Random
from time import monotonic

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from fastunknot.twist.core import (
    Budget, Run, _Meter, _geometry, _rank, build_complex,
)
from fastunknot.twist.tail import tail_homology


def turnback_homology_rank(strands, runs, index):
    """Extract the chosen-E subcomplex without using the tail recurrence.

    The selected positive one-crossing complex has E as a subcomplex. Rebuild
    its state offsets in the documented product order, retain all basis
    elements with chosen state one, and delete every other basis element.
    Its differential contains only the context directions, not the dot map.
    """
    tiny = runs[:index] + [Run(runs[index].generator, 1)] + runs[index+1:]
    complex_ = build_complex(strands, tiny)
    offsets = defaultdict(int)
    indices = {}
    geometry = {}
    for state in product(*[range(abs(r.exponent)+1) for r in tiny]):
        support = sum(1 << j for j, k in enumerate(state) if k)
        if support not in geometry:
            geometry[support] = _geometry(strands, tiny, support)
        dimension = geometry[support].dimension
        degree = sum(k if r.exponent > 0 else -k for k, r in zip(state, tiny))
        offset = offsets[degree]
        offsets[degree] += dimension
        if state[index]:
            for label in range(dimension):
                indices[degree, offset+label] = len(indices)
    columns = []
    for degree, offset in indices:
        column = complex_.columns[degree][offset]
        result = 0
        while column:
            low = column & -column
            target = low.bit_length()-1
            column ^= low
            if (degree+1, target) not in indices:
                raise AssertionError('chosen positive E sector is not a subcomplex')
            result ^= 1 << indices[degree+1, target]
        columns.append(result)
    rank = _rank(columns, _Meter(Budget()))
    return len(indices)-2*rank


def main():
    start = monotonic()
    rng = Random(812026)
    records = []
    for case in range(500):
        strands = rng.randrange(2, 6)
        others = [Run(rng.randrange(1, strands), rng.choice((-2, -1, 1, 2)))
                  for _ in range(rng.randrange(5))]
        index = rng.randrange(len(others)+1)
        w = sum(abs(r.exponent) for r in others)
        selected = Run(rng.randrange(1, strands), w+3)
        runs = others[:index] + [selected] + others[index:]
        answer = tail_homology(strands, runs, run_index=index)
        slope = answer['tail_certificate']['plateau_dimension']
        turnback = turnback_homology_rank(strands, runs, index)
        records.append({
            'case': case, 'strands': strands,
            'runs': [[r.generator, r.exponent] for r in runs],
            'selected': index, 'slope': slope,
            'ordinary_turnback_homology_rank': turnback,
            'equal': slope == turnback,
        })
        if slope != turnback:
            raise AssertionError(records[-1])
    result = {
        'seed': 812026, 'cases': len(records),
        'all_equal': all(r['equal'] for r in records),
        'method': 'ordinary E-subcomplex extracted from selected positive one-crossing complex',
        'seconds': monotonic()-start, 'records': records,
    }
    (Path(sys.argv[1])).write_text(
        json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}))


if __name__ == '__main__':
    main()
