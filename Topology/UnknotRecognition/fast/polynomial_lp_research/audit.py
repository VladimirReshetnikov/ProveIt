"""Fresh exact small-cone, rounding, and authenticated forced-fallback audit."""
import argparse

from fastunknot import bounded_lp
from fastunknot.exact_lp import solve_nonnegative_kernel
from fastunknot.diagram import Diagram
from fastunknot.normal_euler import decide_sector_euler
from fastunknot.normal_euler_verify import verify_sector_euler_certificate
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_crushing_chain import make_crushing_chain, verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing
from fastunknot.positive_ray import extract_positive_ray
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_crushing_search import REDUCTION_RAY
from .common import (ARMS, MASK, Q, pairs, save, source_hashes, small_cases,
    check_lp, bounded_cases, fraction_tree, check_rounding, root_leq, digest)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    output = dict(passed=False, source_sha256=source_hashes(), cones=[], rounding=[], sqrt=[], sources=[])
    for name, matrix, objective in small_cases():
        record = dict(id=name, matrix=[pairs(row) for row in matrix], objective=pairs(objective), queries=[])
        for reduce in (True, False):
            for policy in ARMS:
                options = dict(policy=policy, reduce_rows=reduce)
                if policy == 'polynomial':
                    options['fast_path_pivots'] = 0
                answer = solve_nonnegative_kernel(matrix, objective, **options)
                vertices = check_lp(matrix, objective, answer, reduce_rows=reduce)
                record['queries'].append(dict(options=options, result=answer))
        record['vertices'] = [pairs(point) for point in vertices]
        output['cones'].append(record)
        save(args.output, output)
        print(name, 'exact cone replay passed', flush=True)
    for name, matrix, rhs, exact_point in bounded_cases():
        system = bounded_lp.prepare(matrix, rhs, 3, 1)
        updates = []
        def observe(item):
            if len(updates) >= 12:
                return
            height = max(1, *(abs(a) for row, _ in system.rows for a in row))
            epsilon = Q(1, 2*((system.dimension+1)*height)**(system.dimension+1))
            item['normal'] = next(row for row, b in system.rows
                                  if sum(a*x for a, x in zip(row, item['old_center'])) > b+epsilon)
            check_rounding(item)
            updates.append(fraction_tree(item))
        budget = bounded_lp.Budget()
        decision = bounded_lp.decide(system, budget, observer=observe)
        assert decision['status'] == ('FEASIBLE' if exact_point is not None else 'INFEASIBLE')
        if exact_point is not None:
            assert all(sum(a*x for a, x in zip(row, exact_point)) <= b for row, b in system.rows)
        else:
            # The two original inequalities sum to the contradiction 0 <= -1/16.
            assert all(sum(row[j] for row in matrix) == 0 for j in range(3)) and sum(rhs) < 0
        assert len(updates) == 12
        output['rounding'].append(dict(id=name, matrix=[pairs(row) for row in matrix], rhs=pairs(rhs),
            exact_point=None if exact_point is None else pairs(exact_point),
            decision=fraction_tree(decision), iterations=budget.iterations, updates=updates))
    for numerator in range(-8, 9):
        for square in (Q(1, 9), Q(2), Q(25, 4)):
            value = Q(numerator, 3)
            ceiling = bounded_lp.ceil_divide_sqrt(value, square)
            assert root_leq(value, square, ceiling) and not root_leq(value, square, ceiling-1)
            output['sqrt'].append(dict(value=pairs([value])[0], square=pairs([square])[0], ceiling=ceiling))
    source = layered_torus(2)[0]
    negative = search_euler_transversal(source, MASK, lp_fast_path_pivots=0)
    assert negative['status'] == 'NO_POSITIVE_EULER'
    assert negative['stats']['lp_fallbacks'] > 1 and negative['stats']['transversal_restarts'] > 0
    assert verify_euler_branch_tree(source, negative['certificate'])
    output['sources'].append(dict(id='layered_two_negative', source=source, source_sha256=digest(source),
        allowed_types=MASK, config=dict(lp_fast_path_pivots=0), result=negative))
    circle = Diagram.from_pd([])
    initial = recognize_by_crushing(circle, sector_method='lp', reduce_vertices=False)
    chain = make_crushing_chain(circle, [REDUCTION_RAY], shelling=initial['certificate']['chain']['shelling'])
    assert verify_crushing_chain(circle, chain)
    source = chain['triangulation']
    positive = decide_sector_euler(source, [[0, 2]], lp_fast_path_pivots=0)
    assert positive['status'] == 'POSITIVE_EULER' and positive['stats']['lp_fallbacks'] == 1
    assert verify_sector_euler_certificate(source, positive['certificate'])
    extraction = extract_positive_ray(source, positive['coordinates'])
    complete = make_crushing_chain(circle, [REDUCTION_RAY, extraction['coordinates']], shelling=chain['shelling'])
    assert verify_crushing_chain(circle, complete)
    output['sources'].append(dict(id='one_tet_positive', input_pd=[], source_chain=chain,
        source=source, source_sha256=digest(source), allowed_types=[[0, 2]],
        config=dict(lp_fast_path_pivots=0), result=positive, extraction=extraction, crushing_chain=complete))
    from .check_evidence import check_audit
    output['summary'] = check_audit(output, check_summary=False)
    assert output['source_sha256'] == source_hashes(), 'audited source changed'
    output['passed'] = True
    save(args.output, output)
    print(output['summary'], flush=True)


if __name__ == '__main__':
    main()
