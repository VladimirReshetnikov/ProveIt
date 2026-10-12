"""Independent uncapped source-column parity audit on native dual graphs.

Every source 1-handle is a triangular-face region.  Its original 2-handle
occurrences total at most three.  Modulo two, those dual edges have even
incidence at every 3-handle vertex and at the formal boundary root.  This is
the native occurrence-level form of boundary squared equal to zero; the
audit never replaces geometric counts by signed exponent sums.
"""

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path

from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _edge
from fastunknot.source_core_dual import source_core_dual_graph
from source_core_dual_research.fixtures import stellar_torus


def cap_oracle(prepared, analysed, geometry):
    """Use actual attaching-cycle representatives and explicit parity flips."""
    core = geometry['core']
    owner = {h['vertex']:h['id']+1 for h in core['handles3']}
    edges = {}
    reversed_flags = 0
    for h in core['handles2']:
        flag = h['cycle'][0]
        t, (a,b) = flag['tetrahedron'], flag['local_edge']
        local = _edge(t,a,b)
        ends = [owner.get(prepared['vertex_roots'][4*t+v],0) for v in (a,b)]
        if prepared['edge_orientations'][local]:
            ends.reverse()
            reversed_flags += 1
        weight = analysed['weights'][h['edge']]
        if weight:
            if h['rank'] == 0:
                ends[1] = 0
            else:
                assert h['rank'] == weight
                ends[0] = 0
        else:
            assert h['rank'] == 0
        edges[h['id']] = ends
    return edges, reversed_flags


def fixed_forest(core):
    """Independent explicit-partition replay of the current primal forest."""
    component = list(range(len(core['handles0'])))
    selected = set()
    for h in core['handles1']:
        a,b = (component[v] for v in h['ends'])
        if a != b:
            component = [min(a,b) if x in (a,b) else x for x in component]
            selected.add(h['id'])
    return selected


def audit_case(case):
    prepared = _prepare(case['triangulation'], lambda:None)
    analysed = _coordinates(prepared, case['coordinates'], lambda:None)
    geometry = _parallelity_geometry(prepared, analysed, lambda:None)
    core = geometry['core']
    edges, flips = cap_oracle(prepared, analysed, geometry)
    compiled = source_core_dual_graph(geometry)
    assert {e['two_handle']:[v+1 for v in e['ends']] for e in compiled['edges']} == edges
    columns = defaultdict(Counter)
    for h in core['handles2']:
        for flag in h['cycle']:
            if flag['dimension'] == 1:
                columns[flag['handle']][h['id']] += 1
    tree = fixed_forest(core)
    totals, retained, patterns, triples = Counter(),Counter(),Counter(),Counter()
    details = []
    for c in range(len(core['handles1'])):
        row = columns[c]
        total = sum(row.values())
        assert total <= 3, (case['id'], c, total)
        totals[total] += 1
        if c not in tree:
            retained[total] += 1
        pattern = '+'.join(map(str,sorted(row.values()))) or '0'
        patterns[pattern] += 1
        parity = [0] * (len(core['handles3'])+1)
        for r, count in row.items():
            # A dual loop toggles its endpoint twice and therefore contributes
            # zero, even when its uncapped geometric count is odd.
            for endpoint in edges[r]:
                parity[endpoint] ^= count & 1
        assert not any(parity), (case['id'],c,dict(row),parity)
        if len(row) == 3:
            assert set(row.values()) == {1}
            nonloops = [edges[r] for r in row if edges[r][0] != edges[r][1]]
            if len(nonloops) == 3:
                incident = Counter(v for edge in nonloops for v in edge)
                assert len(incident) == 3 and set(incident.values()) == {2}
                kind = 'triangle'
            elif len(nonloops) == 2:
                assert sorted(nonloops[0]) == sorted(nonloops[1])
                kind = 'parallel_pair_plus_loop'
            else:
                assert not nonloops
                kind = 'three_loops'
            triples[kind] += 1
            details.append(dict(column=c, retained=c not in tree, kind=kind,
                rows=sorted(row), dual_edges=[edges[r] for r in sorted(row)]))
        if pattern in ('1','1+2','3'):
            odd = [r for r,n in row.items() if n % 2]
            assert len(odd) == 1 and edges[odd[0]][0] == edges[odd[0]][1]
    return dict(id=case['id'], tetrahedra=len(case['triangulation']['tetrahedra']),
        three_handles=len(core['handles3']), source_one_handles=len(core['handles1']),
        source_two_handles=len(core['handles2']), reversed_cycle_edge_representatives=flips,
        uncapped_total_histogram={str(k):v for k,v in sorted(totals.items())},
        retained_uncapped_total_histogram={str(k):v for k,v in sorted(retained.items())},
        coefficient_pattern_histogram=dict(sorted(patterns.items())),
        triple_unit_classification=dict(sorted(triples.items())),
        parity_violations=0, triple_unit_columns=details)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    corpus_bytes = (root/'marked_parallelity_research/corpus.json').read_bytes()
    bank = json.loads(corpus_bytes)
    records = [audit_case(case) for case in bank['cases']]
    stellar = []
    for n in (2,4,8):
        raw,rows = stellar_torus(n)
        stellar.append(audit_case(dict(id='stellar_torus/'+str(n),
                                      triangulation=raw,coordinates=rows)))
    assert any(c['triple_unit_classification'].get('triangle',0) for c in stellar)
    counts = Counter(cases=len(records), parity_violations=0)
    total, retained, patterns, triples = Counter(),Counter(),Counter(),Counter()
    for record in records:
        counts['source_columns'] += record['source_one_handles']
        counts['source_rows'] += record['source_two_handles']
        counts['reversed_cycle_edge_representatives'] += record['reversed_cycle_edge_representatives']
        total.update(record['uncapped_total_histogram'])
        retained.update(record['retained_uncapped_total_histogram'])
        patterns.update(record['coefficient_pattern_histogram'])
        triples.update(record['triple_unit_classification'])
    report = dict(source_revision='8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4',
        corpus_sha256=hashlib.sha256(corpus_bytes).hexdigest(), counts=counts,
        all_column_uncapped_total_histogram=dict(sorted(total.items())),
        retained_column_uncapped_total_histogram=dict(sorted(retained.items())),
        coefficient_pattern_histogram=dict(sorted(patterns.items())),
        triple_unit_classification=dict(sorted(triples.items())), cases=records,
        supplementary_stellar_cases=stellar,
        scope='Uncapped original source2handle occurrence columns and occurrence-level source dual cap graph; annular additions excluded.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    summary = {k:v for k,v in report.items() if k not in
               ('cases','source_revision','corpus_sha256','supplementary_stellar_cases')}
    summary['supplementary_stellar_triples'] = {c['id']:c['triple_unit_classification'] for c in stellar}
    print(json.dumps(summary),flush=True)


if __name__ == '__main__':
    main()
