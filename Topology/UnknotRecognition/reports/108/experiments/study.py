"""Independent native extraction for exceptional-column forest selection.

This study authenticates source triangulations with the maintained parser,
extracts raw (uncapped) attaching counts, and checks the existing research
adapter against the finite boundary-kernel construction.  It does not modify
the maintained recognizer or supply a knot verdict.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import sys
import time


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def raw_source_rows(core, tree):
    excluded = set(tree)
    return {h['id']: dict(Counter(f['handle'] for f in h['cycle']
                                 if f['dimension'] == 1
                                 and f['handle'] not in excluded))
            for h in core['handles2']}


def capped(rows):
    return {r: {c: min(2, a) for c, a in row.items()}
            for r, row in rows.items()}


def column_profile(rows, width):
    owners = defaultdict(list)
    for r, row in rows.items():
        for c, count in row.items():
            owners[c].append((r, count))
    patterns = Counter('+'.join(map(str, sorted(a for _, a in values)))
                       for values in owners.values())
    exceptional = []
    for c, values in sorted(owners.items()):
        if len(values) > 2 and any(a == 1 for _, a in values):
            exceptional.append({'column': c, 'rows': [r for r, _ in values],
                                'raw_counts': [a for _, a in values],
                                'all_unit_triple': len(values) == 3
                                and all(a == 1 for _, a in values)})
    return {'rows': len(rows), 'column_namespace': width,
            'nonempty_columns': len(owners),
            'max_support': max(map(len, owners.values()), default=0),
            'max_raw_total': max((sum(a for _, a in v)
                                  for v in owners.values()), default=0),
            'pattern_counts': dict(sorted(patterns.items())),
            'exceptional_columns': exceptional, 'k': len(exceptional),
            'exceptional_incidence_count': sum(len(v['rows']) for v in exceptional)}


def finite_raw_rows(geometry, summary, skeleton, source_core_circle, forest):
    core, profiles = geometry['core'], summary['base_profiles']
    rows = raw_source_rows(core, forest)
    if any(p['boundary_components'] <= 0 for p in profiles):
        return None
    owner = {port: i for i, p in enumerate(profiles) for port in p['core_ports']}
    circles = defaultdict(list)
    offset = len(core['handles2'])
    annular_sources = []
    for i, attachment in enumerate(skeleton['attachment_components']):
        if attachment['kind'] != 'circle':
            continue
        bases = {owner[abs(x) - 1] for x in attachment['word']}
        if len(bases) != 1:
            return None
        base = bases.pop()
        crossings, _ = source_core_circle(geometry, attachment['word'])
        rows[offset + i] = dict(Counter(c['handle'] for c in crossings
                                       if c['handle'] not in forest))
        circles[base].append(i)
        annular_sources.append({'row': offset + i, 'attachment': i,
                                'base_profile': base})
    next_column = len(core['handles1'])
    for base, p in enumerate(profiles):
        if not p['core_ports']:
            continue
        annuli = circles.get(base, [])
        a, b, genus = len(annuli), p['boundary_components'], 1-p['euler_characteristic']
        if p['multiplicity'] != 1 or a > b:
            return None
        dedicated = a if a < b else a - 1
        if genus < dedicated:
            return None
        columns = list(range(next_column, next_column + dedicated))
        next_column += dedicated
        for i, h in zip(annuli, columns):
            rows[offset + i][h] = 1
        if a == b:
            for h in columns:
                rows[offset + annuli[-1]][h] = 1
    return rows, next_column, annular_sources


def independent_tree_oracle(problem, limit=250000):
    """Enumerate top trees and test residual column leaves independently."""
    n = problem['vertices']
    eligible = [i for i, e in enumerate(problem['edges'])
                if e is not None and e[0] != e[1]]
    tried, trees, successful = 0, 0, []
    for chosen in combinations(eligible, n - 1):
        tried += 1
        if tried > limit:
            return {'status': 'CAPPED', 'subsets_tested': tried - 1,
                    'trees_tested': trees}
        labels = list(range(n))
        valid = True
        for r in chosen:
            a, b = [labels[v] for v in problem['edges'][r]]
            if a == b:
                valid = False
                break
            labels = [a if x == b else x for x in labels]
        if not valid or len(set(labels)) != 1:
            continue
        trees += 1
        live = set(range(len(problem['rows']))) - set(chosen)
        while live:
            sums, owner = Counter(), {}
            for r in live:
                for c, a in problem['rows'][r]:
                    sums[c] += a
                    owner[c] = r
            units = [c for c, a in sums.items() if a == 1]
            if not units:
                break
            live.remove(owner[min(units)])
        if not live:
            successful.append(list(chosen))
    return {'status': 'COMPLETE', 'subsets_tested': tried, 'trees_tested': trees,
            'successful_trees': successful, 'exists': bool(successful)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--baseline-fast', type=Path, required=True)
    parser.add_argument('--dual-pack', type=Path, required=True)
    parser.add_argument('--homological-pack', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    fast = args.baseline_fast.resolve()
    dual = args.dual_pack.resolve()
    homo = args.homological_pack.resolve()
    overlay = dual/'native/Topology/UnknotRecognition/fast'
    sys.path[:0] = [str(fast), str(overlay), str(dual/'code/forest_search'),
                    str(homo/'research/experiments')]
    import fastunknot
    fastunknot.__path__.append(str(overlay/'fastunknot'))
    from fastunknot.core_handlebody import _forest, _occurrences
    from fastunknot.disk_bundle_absorption import source_core_circle
    from fastunknot.normal_parallelity import normal_cut_parallelity
    from fastunknot.normal_parallelity_geometry import _parallelity_geometry
    from fastunknot.normal_surface_geometry import _prepare, _coordinates
    from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
    from fastunknot.source_core_dual import source_core_dual_graph
    from source_core_dual_research.matrix_audit import finite_boundary_rows, make_problem
    from source_core_dual_research.source_parity_audit import cap_oracle
    from source_core_dual_research.fixtures import stellar_torus
    from dual_forest_search import solve_degree_two, solve_by_stopping
    from dual_forest_verify import verify
    from core_dual_fixtures import (interior_loop_torus, vertex_link_coordinates,
                                    nested_interior_torus)

    corpus_path = fast/'marked_parallelity_research/corpus.json'
    corpus = json.loads(corpus_path.read_text())['cases']
    cases = [dict(c, family='maintained_corpus') for c in corpus]
    raw = interior_loop_torus()
    for name, coords in [('zero', vertex_link_coordinates(raw)),
                         ('boundary_links', vertex_link_coordinates(raw, boundary=1)),
                         ('interior_links', vertex_link_coordinates(raw, interior=1))]:
        cases.append({'id': 'supplementary/interior_loop_torus/'+name,
                      'family': 'interior_loop_torus', 'triangulation': raw,
                      'coordinates': coords})
    for k in (1, 2, 3, 4, 8):
        raw, coords = stellar_torus(k)
        cases.append({'id': 'supplementary/stellar_torus/'+str(k),
                      'family': 'stellar_torus', 'triangulation': raw,
                      'coordinates': coords})
    for k in (1, 2, 3):
        raw = nested_interior_torus(k)
        cases.append({'id': 'supplementary/nested_interior_torus/'+str(k),
                      'family': 'nested_interior_torus', 'triangulation': raw,
                      'coordinates': vertex_link_coordinates(raw)})

    records = []
    started = time.perf_counter()
    for index, case in enumerate(cases):
        raw, coords = case['triangulation'], case['coordinates']
        prepared = _prepare(raw, lambda: None)
        analysed = _coordinates(prepared, coords, lambda: None)
        geometry = _parallelity_geometry(prepared, analysed, lambda: None)
        core = geometry['core']
        forest, _ = _forest(core, lambda: None)
        rows = raw_source_rows(core, forest)
        assert capped(rows) == _occurrences(core, forest, lambda: None)
        graph = source_core_dual_graph(geometry)
        oracle_edges, _ = cap_oracle(prepared, analysed, geometry)
        assert {e['two_handle']: [v+1 for v in e['ends']]
                for e in graph['edges']} == oracle_edges
        colcounts = defaultdict(Counter)
        for row, values in rows.items():
            for c, a in values.items():
                colcounts[c][row] = a
        for col in colcounts.values():
            assert sum(col.values()) <= 3
            parity = Counter()
            for row, a in col.items():
                for v in oracle_edges[row]:
                    parity[v] += a
            assert all(value % 2 == 0 for value in parity.values())
        record = {'id': case['id'], 'family': case['family'],
                  'native_source': {'triangulation': raw, 'coordinates': coords},
                  'tetrahedra': len(raw['tetrahedra']),
                  'three_handles': len(core['handles3']), 'primal_forest': forest,
                  'source_parity_verified': True}
        candidates = [('source', rows, len(core['handles1']), [])]
        parallelity = normal_cut_parallelity(raw, coords)
        boundary = normal_parallelity_boundary_words(raw, coords)
        assert parallelity['status'] == boundary['status'] == 'COMPLETE'
        extracted = finite_raw_rows(geometry, parallelity['summary'],
                                     boundary['skeleton'], source_core_circle, set(forest))
        existing = finite_boundary_rows(geometry, parallelity['summary'], boundary['skeleton'])
        assert (extracted is None) == (existing is None)
        if extracted is not None:
            rr, width, annuli = extracted
            assert (capped(rr), width) == existing
            candidates.append(('finite_boundary', rr, width, annuli))
        else:
            record['finite_boundary_unsupported'] = True
        for label, rr, width, annuli in candidates:
            # Preserve actual counts for the rank-preservation parity gate.
            # The finite solver itself may cap only after this source record.
            problem, row_ids = make_problem(geometry, rr, width)
            profile = column_profile(rr, width)
            result = solve_degree_two(problem)
            if result['status'] != 'INCONCLUSIVE':
                assert verify(problem, result)
            answer = solve_by_stopping(problem, max_nodes=50000)
            if answer['status'] != 'INCONCLUSIVE':
                assert verify(problem, answer)
            oracle = independent_tree_oracle(problem)
            if oracle['status'] == 'COMPLETE' and answer['status'] != 'INCONCLUSIVE':
                assert oracle['exists'] == (answer['status'] == 'SUCCESS')
            record[label] = {'profile': profile, 'problem': problem,
                             'native_row_ids': row_ids, 'annular_sources': annuli,
                             'degree_two_status': result['status'],
                             'stopping_result': answer, 'tree_oracle': oracle}
        records.append(record)
        print(json.dumps({'index': index, 'id': case['id'],
                          'top_handles': record['three_handles'],
                          'source_k': record['source']['profile']['k'],
                          'boundary_k': record.get('finite_boundary', {}).get('profile', {}).get('k'),
                          'boundary_status': record.get('finite_boundary', {}).get('stopping_result', {}).get('status')}),
              flush=True)
    totals = {}
    for family in ('maintained_corpus', 'interior_loop_torus', 'stellar_torus', 'nested_interior_torus'):
        selected = [r for r in records if r['family'] == family]
        summary = {'cases': len(selected), 'with_top_handles': sum(r['three_handles'] > 0 for r in selected)}
        for label in ('source', 'finite_boundary'):
            included = [r[label] for r in selected if label in r]
            summary[label] = {'cases': len(included),
                'k_distribution': dict(sorted(Counter(str(r['profile']['k']) for r in included).items(), key=lambda x: int(x[0]))),
                'exceptional_columns': sum(r['profile']['k'] for r in included),
                'max_raw_total': max((r['profile']['max_raw_total'] for r in included), default=0),
                'max_support': max((r['profile']['max_support'] for r in included), default=0),
                'all_exceptions_unit_triples': all(e['all_unit_triple'] for r in included for e in r['profile']['exceptional_columns']),
                'stopping_statuses': dict(Counter(r['stopping_result']['status'] for r in included)),
                'degree_two_statuses': dict(Counter(r['degree_two_status'] for r in included)),
                'oracle_complete': sum(r['tree_oracle']['status'] == 'COMPLETE' for r in included)}
        totals[family] = summary
    payload = {'scope': 'Fresh native source reconstruction; finite graph/matrix claims only. All top-tree search outcomes fix the recorded primal forest.',
               'baseline_revision': 'c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5',
               'corpus_sha256': digest(corpus_path),
               'dependencies': {str(p): digest(p) for p in [Path(__file__), corpus_path,
                    fast/'fastunknot/core_handlebody.py', fast/'fastunknot/bundle_boundary_kernel.py',
                    overlay/'fastunknot/source_core_dual.py',
                    overlay/'source_core_dual_research/matrix_audit.py',
                    dual/'code/forest_search/dual_forest_search.py',
                    dual/'code/forest_search/dual_forest_verify.py']},
               'elapsed_seconds': time.perf_counter() - started,
               'totals': totals, 'cases': records}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + '\n')
    print(json.dumps(totals, indent=2), flush=True)


if __name__ == '__main__':
    main()
