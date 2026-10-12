"""Native source and finite-interface unsigned matrix scope for forest search.

Run from fast/: python -m source_core_dual_research.matrix_audit --output FILE
Optionally pass --solver-dir pointing to the accompanying finite solver.
The optional results concern the supplied graph/matrix operation only.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

from fastunknot.core_handlebody import _forest, _occurrences
from fastunknot.disk_bundle_absorption import source_core_circle
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.source_core_dual import source_core_dual_graph


def profile(rows, width):
    support, totals = Counter(), Counter()
    for row in rows.values():
        for c, value in row.items():
            support[c] += 1
            totals[c] += value
    histogram = Counter(support.values())
    histogram[0] += width - len(support)
    return dict(rows=len(rows), column_namespace=width,
        max_row_support=max(support.values(), default=0),
        max_capped_occurrence_total=max(totals.values(), default=0),
        column_support_histogram={str(k): v for k, v in sorted(histogram.items())},
        degree_two=all(v <= 2 for v in support.values()))


def finite_boundary_rows(geometry, summary, skeleton):
    """Research adapter matching the existing boundary-kernel construction.

    Source rows retain their original IDs and later annular rows are marked
    nondeletable in the dual graphic matroid.  The permanently even omitted
    genus columns are inert for unit peeling and need not be materialized.
    """
    core = geometry['core']
    tree, _ = _forest(core, lambda: None)
    rows = _occurrences(core, tree, lambda: None)
    source_tree = set(tree)
    profiles = summary['base_profiles']
    if any(p['boundary_components'] <= 0 for p in profiles):
        return None
    owner = {port: i for i, p in enumerate(profiles) for port in p['core_ports']}
    circles = {}
    offset = len(core['handles2'])
    for i, attachment in enumerate(skeleton['attachment_components']):
        if attachment['kind'] != 'circle':
            continue
        bases = {owner[abs(x)-1] for x in attachment['word']}
        if len(bases) != 1:
            return None
        base = bases.pop()
        crossings, _ = source_core_circle(geometry, attachment['word'])
        row = {}
        for crossing in crossings:
            h = crossing['handle']
            if h not in source_tree:
                row[h] = min(2, row.get(h, 0) + 1)
        rows[offset+i] = row
        circles.setdefault(base, []).append(i)
    next_column = len(core['handles1'])
    for base, p in enumerate(profiles):
        if not p['core_ports']:
            continue
        annuli = circles.get(base, [])
        a, b, genus = len(annuli), p['boundary_components'], 1-p['euler_characteristic']
        if p['multiplicity'] != 1 or a > b:
            return None
        dedicated = a if a < b else a-1
        if genus < dedicated:
            return None
        columns = list(range(next_column, next_column+dedicated))
        next_column += dedicated
        for i, h in zip(annuli, columns):
            rows[offset+i][h] = 1
        if a == b:
            for h in columns:
                rows[offset+annuli[-1]][h] = 1
    return rows, next_column


def make_problem(geometry, rows, columns):
    graph = source_core_dual_graph(geometry)
    ends = {e['two_handle']: [v+1 for v in e['ends']] for e in graph['edges']}
    ids = sorted(rows)
    return dict(vertices=graph['three_handles']+1, columns=columns,
        edges=[ends.get(r) for r in ids],
        rows=[[[c, a] for c, a in sorted(rows[r].items())] for r in ids]), ids


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--solver-dir', type=Path)
    args = parser.parse_args()
    if args.solver_dir:
        sys.path.insert(0, str(args.solver_dir.resolve()))
        from dual_forest_search import solve_degree_two, solve_by_stopping
        from dual_forest_verify import verify
    root = Path(__file__).resolve().parents[1]
    source = (root / 'marked_parallelity_research/corpus.json').read_bytes()
    bank = json.loads(source)
    counts, cases = Counter(), []
    for case in bank['cases']:
        prepared = _prepare(case['triangulation'], lambda: None)
        analysed = _coordinates(prepared, case['coordinates'], lambda: None)
        geometry = _parallelity_geometry(prepared, analysed, lambda: None)
        core = geometry['core']
        tree, _ = _forest(core, lambda: None)
        rows = _occurrences(core, tree, lambda: None)
        source_profile = profile(rows, len(core['handles1'])-len(tree))
        raw_totals = Counter()
        removed = set(tree)
        for h in core['handles2']:
            for flag in h['cycle']:
                if flag['dimension'] == 1 and flag['handle'] not in removed:
                    raw_totals[flag['handle']] += 1
        source_profile['max_raw_occurrence_total'] = max(raw_totals.values(), default=0)
        assert source_profile['max_raw_occurrence_total'] <= 3
        record = dict(id=case['id'], three_handles=len(core['handles3']),
                      source_forest=tree, source_matrix=source_profile)
        counts['source_max_support_'+str(source_profile['max_row_support'])] += 1
        counts['source_degree_two'] += source_profile['degree_two']
        if core['handles3']:
            counts['three_handle_cases'] += 1
            counts['three_handle_degree_two'] += source_profile['degree_two']
            candidates = [('source', rows, len(core['handles1']))]
            packet = normal_cut_parallelity(case['triangulation'], case['coordinates'])
            boundary = normal_parallelity_boundary_words(case['triangulation'], case['coordinates'])
            augmented = finite_boundary_rows(geometry, packet['summary'], boundary['skeleton'])
            if augmented:
                aa, width = augmented
                record['finite_boundary_matrix'] = profile(aa, width-len(tree))
                candidates.append(('finite_boundary', aa, width))
            if args.solver_dir:
                for name, values, width in candidates:
                    problem, ids = make_problem(geometry, values, width)
                    result = solve_degree_two(problem)
                    if result['status'] != 'INCONCLUSIVE':
                        assert verify(problem, result)
                    record[name+'_degree_two_result'] = result
                    result = solve_by_stopping(problem, max_nodes=100000)
                    if result['status'] != 'INCONCLUSIVE':
                        assert verify(problem, result)
                    record[name+'_stopping_result'] = result
                    record[name+'_row_ids'] = ids
                    record[name+'_problem'] = problem
            print(json.dumps({k:v for k,v in record.items() if k in
                ('id','three_handles','source_matrix','finite_boundary_matrix')}), flush=True)
        cases.append(record)
    report = dict(source_revision='8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4',
        corpus_sha256=hashlib.sha256(source).hexdigest(), counts=counts, cases=cases,
        scope='Original source 2-handles after fixed native 0/1 forest; augmented matrices separately labelled.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(counts), flush=True)


if __name__ == '__main__':
    main()
