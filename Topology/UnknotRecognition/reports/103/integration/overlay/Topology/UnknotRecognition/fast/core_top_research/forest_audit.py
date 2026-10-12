"""Native applicability of the restricted forest planner, strictly core-only.

The experiment constructs actual source cores, fixes the maintained primal
forest, and compares the joint forest strategy with the ordinary rooted dual
queue followed by raw row cancellation. It does not classify attached bundles,
transport boundary patterns, or report a whole-cut/knot-recognition verdict.
"""

import argparse
from collections import Counter
import json
from pathlib import Path
import platform
import sys
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-dir', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('forest_exchange_audit.json'))
    parser.add_argument('--subdivisions', type=int, default=8)
    args = parser.parse_args()
    if args.subdivisions < 0:
        parser.error('--subdivisions must be nonnegative')
    sys.path.insert(0, str(args.fast_dir.resolve()))
    from fastunknot.core_forest_exchange import plan_forest_exchange
    from fastunknot.core_forest_exchange_verify import verify_forest_exchange
    from fastunknot.core_handlebody import _forest, _occurrences, capped_cancellation_plan
    from fastunknot.core_handlebody import core_handlebody_certificate
    from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
    from fastunknot.core_top_reduction import source_core_top_incidence, rooted_top_plan
    from fastunknot.core_top_reduction_verify import replay_core_top_reduction
    from fastunknot.integer_codec import json_safe
    from fastunknot.normal_parallelity import normal_cut_parallelity

    counts, results = Counter(), []
    started = time.perf_counter()

    def audit_case(case, family):
        initial = time.perf_counter()
        raw, coordinates = case['triangulation'], case['coordinates']
        geometry = normal_cut_parallelity(raw, coordinates)['geometry']
        incidence = source_core_top_incidence(raw, coordinates, geometry)
        core = geometry['core']
        primal_forest, _ = _forest(core, lambda: None)
        rows = _occurrences(core, primal_forest, lambda: None)
        three = list(range(len(incidence['three_handles'])))
        ends = {edge['id']: [v for v in edge['ends'] if v is not None]
                for edge in incidence['two_handles']}
        plan = plan_forest_exchange(three, ends, rows)
        if not verify_forest_exchange(three, ends, rows, plan['certificate']):
            raise ArithmeticError('native graph certificate failed replay: ' + case['id'])
        ordinary_moves, ordinary_retained, _ = rooted_top_plan(incidence)
        ordinary_raw = capped_cancellation_plan({e: rows[e] for e in ordinary_retained})
        ordinary_complete = not ordinary_raw['remaining_rows']
        proof = plan['certificate']
        rec = dict(id=case['id'], family=family, tetrahedra=len(raw['tetrahedra']),
                   handles=[len(core['handles' + str(i)]) for i in range(4)],
                   primal_forest=primal_forest,
                   capped_row_length_histogram=dict(Counter(sum(row.values())
                                                           for row in rows.values())),
                   forced_long_rows=sum(sum(row.values()) > 2 for row in rows.values()),
                   planner_status=plan['status'], planner_reason=plan.get('reason'),
                   planner_stats=plan['stats'], planner_certificate=proof,
                   graph_certificate_replayed=True,
                   ordinary_dual_moves=ordinary_moves,
                   ordinary_raw_complete=ordinary_complete,
                   ordinary_raw_remaining_rows=ordinary_raw['remaining_rows'])
        if proof['kind'] in ('complete', 'short_row_rank_obstruction'):
            retained = sorted(set(rows) - set(proof['dual_forest']))
            top_proof = dict(schema='normal-core-top-reduction-v1',
                             input_sha256=incidence['input_sha256'],
                             moves=proof['two_three_cancellations'],
                             surviving_two_handles=retained)
            reduced = replay_core_top_reduction(raw, coordinates, geometry, top_proof)
            if reduced is None:
                raise ArithmeticError('chosen native dual forest failed source replay')
            rec['chosen_dual_forest_source_replayed'] = True
            if plan['status'] == 'COMPLETE':
                core_answer = core_handlebody_certificate(reduced['core'])
                if core_answer['status'] != 'COMPLETE':
                    raise ArithmeticError('complete joint plan failed maintained core consumer')
                if not verify_core_handlebody_certificate(
                        reduced['core'], core_answer['certificate']):
                    raise ArithmeticError('chosen core census failed independent replay')
                rec['core_genera'] = [component['genus'] for component in core_answer['components']]
                rec['core_certificate_replayed'] = True
        rec['seconds'] = time.perf_counter() - initial
        results.append(rec)
        counts[family + '_cases'] += 1
        counts[family + '_graph_replays'] += 1
        counts[family + '_planner_' + plan['status']] += 1
        if plan['status'] != 'COMPLETE':
            counts[family + '_' + plan['reason']] += 1
        if ordinary_complete:
            counts[family + '_ordinary_core_complete'] += 1
        if plan['status'] == 'COMPLETE' and not ordinary_complete:
            counts[family + '_planner_improves_core_coverage'] += 1
        if plan['status'] != 'COMPLETE' and ordinary_complete:
            counts[family + '_restriction_misses_ordinary_success'] += 1

    corpus_path = args.fast_dir / 'marked_parallelity_research/corpus.json'
    corpus = json.loads(corpus_path.read_text())['cases']
    for case in corpus:
        audit_case(case, 'corpus')
    print(json.dumps(dict(stage='corpus_completed', counts=counts)), flush=True)

    subdivision_status = 'disabled'
    if args.subdivisions:
        try:
            import regina
        except ImportError:
            subdivision_status = 'unavailable: optional Regina generator is not installed'
        else:
            from normal_orbit_research.fixtures import (
                layered_torus, regina_triangulation, export_triangulation)
            raw, _ = layered_torus(1)
            triangulation = regina_triangulation(raw)
            for q in range(1, args.subdivisions + 1):
                tetrahedron = min(triangulation.tetrahedra(), key=lambda t:
                    (sum(t.vertex(v).isBoundary() for v in range(4)), t.index()))
                if not triangulation.pachner(tetrahedron):
                    raise ArithmeticError('independent 1-4 source generator failed')
                raw = export_triangulation(triangulation)
                source = dict(id='empty_layered_torus_subdivision_' + str(q),
                              triangulation=raw, coordinates=[[0] * 7 for _ in raw['tetrahedra']])
                audit_case(source, 'subdivision')
                results[-1]['source'] = source
            subdivision_status = 'completed with Regina ' + regina.versionString()
    report = dict(scope='native source core applicability; no attached-bundle or whole-cut verdict',
                  python=platform.python_version(), source_case_count=len(corpus),
                  fixed_primal_forest='maintained core_handlebody._forest',
                  ordinary_comparator='rooted_top_plan then capped_cancellation_plan',
                  subdivision_status=subdivision_status, counts=counts,
                  seconds=time.perf_counter() - started, cases=results)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(report), indent=2) + '\n')
    print(json.dumps(dict(counts=counts, seconds=report['seconds'],
                          subdivision_status=subdivision_status)), flush=True)


if __name__ == '__main__':
    main()
