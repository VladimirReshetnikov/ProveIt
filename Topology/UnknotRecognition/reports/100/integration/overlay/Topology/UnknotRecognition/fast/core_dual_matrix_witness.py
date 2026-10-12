"""Exact source witness that dual-forest choice changes raw eliminability.

The five-tetrahedron fixture is an actual solid torus.  The canonical BFS
forest leaves a rectangular raw matrix with no unit-permanent maximal minor;
the maximum-weight forest leaves several unit-permanent maximal minors.
Exhaustive capped-pivot search independently confirms the contrast here.
"""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations
import json
from math import prod
from pathlib import Path

from core_dual_fixtures import interior_loop_torus, vertex_link_coordinates
from fastunknot.core_dual_forest import core_dual_forest
from fastunknot.core_dual_forest_verify import replay_core_dual_forest
from fastunknot.core_handlebody import _forest
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity


def maximal_permanents(matrix):
    m, n = len(matrix), len(matrix[0])
    answer = []
    for chosen in combinations(range(n), m):
        value = sum(prod(matrix[r][chosen[c]] for r, c in enumerate(permutation))
                    for permutation in permutations(range(m)))
        answer.append(dict(columns=list(chosen), permanent=value))
    return answer


@lru_cache(None)
def exhaustive_eliminable(matrix):
    if not matrix:
        return True
    m, n = len(matrix), len(matrix[0])
    for r in range(m):
        for c in range(n):
            if matrix[r][c] != 1:
                continue
            reduced = tuple(tuple(min(2, matrix[i][j] + matrix[i][c] * matrix[r][j])
                                  for j in range(n) if j != c)
                            for i in range(m) if i != r)
            if exhaustive_eliminable(reduced):
                return True
    return False


def witness():
    raw = interior_loop_torus()
    rows = vertex_link_coordinates(raw)
    parallelity = normal_cut_parallelity(raw, rows, record_certificate=True)
    assert parallelity['status'] == 'COMPLETE'
    assert verify_normal_cut_parallelity(raw, rows, parallelity['certificate'])
    geometry, core = parallelity['geometry'], parallelity['geometry']['core']
    primal, _ = _forest(core, lambda: None)
    columns = [i for i in range(len(core['handles1'])) if i not in primal]
    matrix = [[Counter(flag['handle'] for flag in h['cycle']
                       if flag['dimension'] == 1)[column] for column in columns]
              for h in core['handles2']]
    expected = [[0, 0, 1, 0, 0], [1, 1, 0, 0, 0], [0, 1, 0, 1, 1],
                [1, 0, 1, 1, 1], [0, 1, 1, 1, 0]]
    assert matrix == expected
    result = dict(triangulation=raw, coordinates=rows,
                  canonical_primal_forest=primal, source_one_handle_columns=columns,
                  source_literal_matrix=matrix, strategies={})
    for strategy in ('bfs', 'max_weight'):
        dual = core_dual_forest(geometry, strategy=strategy)
        assert replay_core_dual_forest(geometry, dual['certificate']) == dual['core']
        surviving = dual['certificate']['surviving_two_handles']
        residual = [matrix[r] for r in surviving]
        minors = maximal_permanents(residual)
        totals = [sum(row[c] for row in residual) for c in range(len(columns))]
        exact = exhaustive_eliminable(tuple(map(tuple, residual)))
        assert exact == any(m['permanent'] == 1 for m in minors)
        whole = normal_cut_handlebodies(raw, rows, dual_strategy=strategy,
                                       record_certificate=True)
        record = dict(dual_certificate=dual['certificate'],
                      source_two_handle_rows=surviving, residual_matrix=residual,
                      column_totals=totals,
                      all_rows_form_stopping_set=all(value != 1 for value in totals),
                      maximal_minor_permanents=minors, raw_eliminable=exact,
                      status=whole['status'], reason=whole.get('reason'))
        if whole['status'] == 'COMPLETE':
            assert verify_normal_cut_handlebodies(raw, rows, whole['certificate'])
            core_proof = whole['certificate']['downstream']['core']
            record.update(census=whole['census'], core_certificate=core_proof,
                          source_labeled_cancellations=[[surviving[r], c]
                                                        for r, c in core_proof['cancellations']])
        result['strategies'][strategy] = record
    assert result['strategies']['bfs']['raw_eliminable'] is False
    assert result['strategies']['max_weight']['raw_eliminable'] is True
    result['exhaustive_pivot_search'] = exhaustive_eliminable.cache_info()._asdict()
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    Path(args.output).write_text(json.dumps(witness(), indent=2) + '\n')


if __name__ == '__main__':
    main()
