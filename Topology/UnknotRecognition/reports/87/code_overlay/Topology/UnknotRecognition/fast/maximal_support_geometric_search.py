"""Bounded reproducible search for source zeros missed by two-row closure.

Optional Regina generates larger genuine solid-torus triangulations. Every
accepted example is independently checked from exported source matching data.
The search records seeds, actual moves, source face pairings and tested type
assignments. Absence within this bounded sample is only a negative experiment.
"""

import argparse
from collections import Counter
from copy import deepcopy
import json
from pathlib import Path
import random
from time import perf_counter

from fastunknot.normal_sector import _nullspace
from fastunknot.sector_matching_support import _combined_closure, _kernel_equations
from fastunknot.sector_maximal_support import certify_nonnegative_kernel_support, certify_maximal_support
from fastunknot.sector_sparse import PreparedSectorSource
from normal_orbit_research.fixtures import (
    boundary_cap, export_triangulation, layered_torus, regina_triangulation,
)


def source_family(rng):
    import regina
    for size in (12, 20, 32):
        raw, coordinates = layered_torus(size)
        yield dict(kind='fibonacci', size=size, triangulation=raw)
        for _ in range(4):
            raw, coordinates = boundary_cap(raw, coordinates)
        yield dict(kind='fibonacci-plus-four-caps', size=size,
                   triangulation=raw)
    for chain in range(8):
        raw, _ = layered_torus(2+chain % 3)
        tri = regina_triangulation(raw)
        moves = []
        for target in (12, 20, 28, 36):
            attempts = 0
            while tri.size() < target:
                if attempts > 20*target or rng.randrange(12) == 0:
                    index = rng.randrange(tri.size())
                    assert tri.pachner(tri.tetrahedron(index))
                    moves.append(['14', index])
                else:
                    index = rng.randrange(tri.countTriangles())
                    if tri.pachner(tri.triangle(index)):
                        moves.append(['23', index])
                attempts += 1
            yield dict(kind='pachner-chain', chain=chain, initial_tetrahedra=2+chain % 3,
                       target=target, moves=deepcopy(moves), isosig=tri.isoSig(),
                       triangulation=export_triangulation(tri))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seed', default='maximal-support-geometric-20261012')
    parser.add_argument('--seconds', type=float, default=180)
    parser.add_argument('--sectors', type=int, default=128)
    parser.add_argument('--minimum-dimension', type=int, default=4)
    parser.add_argument('--iterate-incumbent', action='store_true',
                        help='also re-RREF and repeat pair closure after each coordinate restriction')
    args = parser.parse_args()
    if args.seconds <= 0 or args.sectors <= 0 or args.minimum_dimension < 1:
        parser.error('budgets and minimum dimension must be positive')
    import regina
    rng = random.Random(args.seed)
    start = perf_counter()
    result = dict(schema='maximal-support-geometric-search-v1', seed=args.seed,
        regina=regina.versionString(), seconds_limit=args.seconds,
        sectors_per_source=args.sectors, minimum_dimension=args.minimum_dimension,
        iterate_incumbent=args.iterate_incumbent,
        sources=[], queries=[], found=None)
    dimensions = Counter()
    tested = easy = proposals = 0
    stop = False
    for specification in source_family(rng):
        if perf_counter()-start >= args.seconds:
            break
        index = len(result['sources'])
        result['sources'].append(specification)
        raw = specification['triangulation']
        source = PreparedSectorSource(raw)
        count = len(raw['tetrahedra'])
        for sample in range(args.sectors):
            if perf_counter()-start >= args.seconds:
                stop = True
                break
            signature = [rng.randrange(3) for _ in range(count)]
            support = list(enumerate(signature))
            kernel = source.build(support)
            dimension = len(kernel.basis)
            dimensions[dimension] += 1
            tested += 1
            if dimension < args.minimum_dimension:
                continue
            rows = _kernel_equations(kernel.basis, count, lambda: None)
            forced, _ = _combined_closure(rows, lambda: None)
            keep = [j for j in range(count) if j not in forced]
            first_forced = len(forced)
            rounds = 1
            if args.iterate_incumbent:
                while keep:
                    restricted_rows = [[row[j] for j in keep] for row in rows]
                    restricted_basis = _nullspace(restricted_rows, len(keep))
                    new_rows = _kernel_equations(restricted_basis, len(keep), lambda: None)
                    extra, _ = _combined_closure(new_rows, lambda: None)
                    if not extra:
                        break
                    keep = [j for i, j in enumerate(keep) if i not in extra]
                    rounds += 1
                forced = set(range(count))-set(keep)
            reduced = [[row[j] for j in keep] for row in rows]
            basis = _nullspace(reduced, len(keep))
            candidate = [sum(row[j] for row in basis) for j in range(len(keep))]
            if not keep or all(x > 0 for x in candidate):
                easy += 1
                result['queries'].append(dict(source=index, sample=sample, signature=signature,
                    raw_dimension=dimension, incumbent_forced=len(forced),
                    incumbent_first_pass_forced=first_forced, incumbent_rounds=rounds,
                    complete_by='empty or exact positive sum of restricted kernel basis'))
                continue
            proposals += 1
            complete = certify_nonnegative_kernel_support(rows, width=count, solver='scipy')
            query = dict(source=index, sample=sample, signature=signature,
                         raw_dimension=dimension, incumbent_forced=len(forced),
                         incumbent_first_pass_forced=first_forced, incumbent_rounds=rounds,
                         exact_status=complete['status'])
            if complete['status'] == 'COMPLETE':
                exact = complete['retained_indices']
                extra = sorted(set(keep)-set(exact))
                query.update(exact_retained=exact, extra_forced=extra,
                             effective_dimension=complete['stats']['effective_dimension'])
                if extra:
                    source_proof = certify_maximal_support(raw, support, source=source)
                    assert source_proof['status'] == 'COMPLETE'
                    assert source_proof['retained_indices'] == exact
                    result['found'] = dict(query=query, specification=specification,
                                          allowed_types=support, result=source_proof)
                    stop = True
            result['queries'].append(query)
            if stop:
                break
        if stop:
            break
    result.update(elapsed_seconds=perf_counter()-start, sectors_tested=tested,
                  easy_exact_supports=easy, LP_proposals=proposals,
                  raw_dimension_histogram=dict(sorted(dimensions.items())))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ('elapsed_seconds', 'sectors_tested',
            'easy_exact_supports', 'LP_proposals', 'raw_dimension_histogram')}))
    print('FOUND' if result['found'] is not None else 'NO EXAMPLE IN THIS BOUNDED SAMPLE')


if __name__ == '__main__':
    main()
