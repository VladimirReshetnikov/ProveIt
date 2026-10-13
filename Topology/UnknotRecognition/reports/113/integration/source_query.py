#!/usr/bin/env python3
"""Additive source-first adapter; never returns an unknot/knottedness verdict."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from projective_ports import Prepared,ResourceLimit
from projective_ports.source import (Source,compile_two_block,
                                     compile_variable_separator,extreme_witness)
from projective_ports.verify import verify_vector


def solve_source(source: Source, objective, *, zeros=(), left=None, masters=None,
                 max_supports=1_000_000, max_candidates=100_000,
                 ray_method='support', check=lambda:None):
    """Compile, search, reconstruct, and independently check one source query.

    Exactly one of left or masters must be provided. Invalid source partitions
    raise ValueError; exhausted budgets return INCONCLUSIVE. The caller must
    authenticate the original source and perform all geometric interpretation.
    Repeated queries should retain Compilation and Prepared objects instead.
    """
    if (left is None)==(masters is None):
        raise ValueError('provide exactly one source partition: left or masters')
    try:
        check()
        compilation=(compile_two_block(source,left) if left is not None
                     else compile_variable_separator(source,masters))
        costs,master,excluded=compilation.query(objective,zeros)
        prepared=Prepared(compilation.blocks,max_supports=max_supports,
                          max_candidates=max_candidates,ray_method=ray_method,check=check)
        answer=prepared.solve(costs,master=master,zeros=excluded,check=check)
        if answer['status']=='NO_POSITIVE':
            return {'schema':'projective-source-query-v1','status':'NO_POSITIVE',
                    'scope':'specified complete algebraic query only','stats':prepared.stats}
        witness=extreme_witness(source,compilation.reconstruct(answer['vectors']),objective,check=check)
        if not verify_vector(source.n,source.equations,source.conflicts,objective,
                             witness['coordinates'],zeros=zeros,extreme=True):
            raise ArithmeticError('independent source replay rejected producer output')
        return {'schema':'projective-source-query-v1','status':'POSITIVE',
                'scope':'source matching ray; geometric authentication remains external',
                'coordinates':list(witness['coordinates']),'zeros':list(zeros),
                'descent':witness['descent'],'stats':prepared.stats}
    except ResourceLimit as exc:
        return {'schema':'projective-source-query-v1','status':'INCONCLUSIVE','reason':str(exc)}


if __name__=='__main__':
    import json
    from projective_ports.fixtures import capped_solid_torus,matching,euler
    tri=capped_solid_torus()
    print(json.dumps(solve_source(matching(tri),euler(tri),zeros=(10,2),left=range(7)),indent=2))
