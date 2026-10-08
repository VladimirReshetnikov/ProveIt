"""Budget-safe composition of the kernel and exact reduced homology."""
from __future__ import annotations
from time import monotonic
from .core import Braid, kernelize
from .cube import ResourceLimit, reduced_khovanov


def recognize(braid: Braid, *, max_crossings: int | None = 12,
              max_generators: int | None = 200000, seconds: float | None = None,
              check_d_squared: bool = False) -> dict:
    start = monotonic()
    result = kernelize(braid)
    if result['status'] != 'CORE':
        result['seconds'] = monotonic()-start
        return result
    memo, computations, unknown = {}, [], False
    for item in result['factors']:
        f = Braid.checked(item['strands'], item['word'])
        key = (f.strands, f.word)
        if key in memo:
            rank = memo[key]
        else:
            try:
                # B2 exponent is a complete invariant of its braid element.
                if f.strands == 2:
                    rank = 1 if abs(f.exponent) == 1 else 3
                    record = {'method': 'two-braid-exponent', 'reduced_rank_lower_bound': rank}
                else:
                    remaining = None if seconds is None else max(0., seconds-(monotonic()-start))
                    record = reduced_khovanov(f, max_crossings=max_crossings,
                         max_generators=max_generators, seconds=remaining,
                         check_d_squared=check_d_squared)
                    rank = record['reduced_rank']
                computations.append({'factor': f.to_json(), **record})
                memo[key] = rank
            except ResourceLimit as error:
                computations.append({'factor': f.to_json(), 'resource_limit': str(error)})
                unknown = True
                continue
        if rank != 1:
            result.update(status='KNOTTED', method='kernel-factor-obstruction',
                          factor_computations=computations, seconds=monotonic()-start)
            return result
    result.update(status='UNKNOWN' if unknown else 'UNKNOT',
                  method='kernel-budget' if unknown else 'kernel-all-factors-trivial',
                  factor_computations=computations, seconds=monotonic()-start)
    return result
