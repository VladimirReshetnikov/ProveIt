"""Independently authenticate the three native annular stopping obstructions.

This audit reconstructs source matrices using explicit component partitions
and the independent geometric circle tracer.  It authenticates both source
packets before comparing against the graph/matrix search input.  The negative
result concerns this fixed raw boundary kernel, not the underlying manifold.
"""

import argparse
from collections import Counter
import json
from pathlib import Path
import sys

from fastunknot.disk_bundle_absorption_verify import reconstruct_core_circle
from fastunknot.integer_codec import json_safe
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _edge
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words


def reconstruct(case, geometry, summary, skeleton):
    core = geometry['core']
    component = list(range(len(core['handles0'])))
    tree = []
    for h in core['handles1']:
        a, b = (component[v] for v in h['ends'])
        if a != b:
            component = [min(a,b) if x in (a,b) else x for x in component]
            tree.append(h['id'])
    on_tree = set(tree)
    rows = {}
    for h in core['handles2']:
        counts = Counter(f['handle'] for f in h['cycle']
                         if f['dimension'] == 1 and f['handle'] not in on_tree)
        rows[h['id']] = {c:min(2,n) for c,n in counts.items()}
    bases = summary['base_profiles']
    port_base = {p:i for i,b in enumerate(bases) for p in b['core_ports']}
    annular = {}
    offset = len(core['handles2'])
    for index, attachment in enumerate(skeleton['attachment_components']):
        if attachment['kind'] != 'circle':
            continue
        base_choices = {port_base[abs(x)-1] for x in attachment['word']}
        assert len(base_choices) == 1
        base = base_choices.pop()
        traced = reconstruct_core_circle(geometry, attachment)
        assert traced is not None
        counts = Counter(x['handle'] for x in traced[0] if x['handle'] not in on_tree)
        rows[offset+index] = {c:min(2,n) for c,n in counts.items()}
        annular.setdefault(base, []).append(index)
    next_column = len(core['handles1'])
    for i, base in enumerate(bases):
        if not base['core_ports']:
            continue
        circles = annular.get(i, [])
        number, boundary = len(circles), base['boundary_components']
        assert base['multiplicity'] == 1 and 0 <= number <= boundary
        retained = min(number, boundary-1)
        assert 1-base['euler_characteristic']-retained >= 0
        for j in range(retained):
            column = next_column+j
            rows[offset+circles[j]][column] = 1
            if number == boundary:
                rows[offset+circles[-1]][column] = 1
        next_column += retained

    # A different local edge representative from the native compiler is used:
    # the first 0-handle flag of each actual attaching cycle, with explicit
    # signed orientation recovered from the original face pairing.
    prepared = _prepare(case['triangulation'], lambda: None)
    analysed = _coordinates(prepared, case['coordinates'], lambda: None)
    owners = {h['vertex']:h['id']+1 for h in core['handles3']}
    edges = {}
    for h in core['handles2']:
        flag = h['cycle'][0]
        t, (a,b) = flag['tetrahedron'], flag['local_edge']
        ends = [owners.get(prepared['vertex_roots'][4*t+v],0) for v in (a,b)]
        if prepared['edge_orientations'][_edge(t,a,b)]:
            ends.reverse()
        w = analysed['weights'][h['edge']]
        if w:
            if h['rank'] == 0:
                ends[1] = 0
            else:
                assert h['rank'] == w
                ends[0] = 0
        edges[h['id']] = ends
    ids = sorted(rows)
    problem = dict(vertices=len(core['handles3'])+1, columns=next_column,
        edges=[edges.get(r) for r in ids],
        rows=[[[c,v] for c,v in sorted(rows[r].items())] for r in ids])
    return problem, ids, tree


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--matrix-audit', type=Path, required=True)
    parser.add_argument('--solver-dir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    sys.path.insert(0, str(args.solver_dir.resolve()))
    from dual_forest_verify import verify
    root = Path(__file__).resolve().parents[1]
    bank = json.loads((root/'marked_parallelity_research/corpus.json').read_text())
    cases = {c['id']:c for c in bank['cases']}
    audit = json.loads(args.matrix_audit.read_text())
    args.output.mkdir(parents=True, exist_ok=True)
    records = []
    for record in audit['cases']:
        result = record.get('finite_boundary_stopping_result', {})
        if result.get('status') != 'NO_FOREST':
            continue
        case = cases[record['id']]
        raw, coordinates = case['triangulation'], case['coordinates']
        p = normal_cut_parallelity(raw, coordinates, record_certificate=True)
        b = normal_parallelity_boundary_words(raw, coordinates, record_certificate=True)
        assert verify_normal_cut_parallelity(raw, coordinates, p['certificate'])
        assert verify_parallelity_boundary_words(raw, coordinates, b['certificate'])
        problem, ids, tree = reconstruct(case, p['geometry'], p['summary'], b['skeleton'])
        assert problem == record['finite_boundary_problem']
        assert ids == record['finite_boundary_row_ids']
        assert tree == record['source_forest']
        assert verify(problem, result)
        proof = result['certificate']
        assert proof['kind'] == 'blocked'
        witness = proof['witness']
        assert all(problem['edges'][r] is None for r in witness)
        totals = Counter()
        for r in witness:
            for c, a in problem['rows'][r]:
                totals[c] += a
        assert totals and all(a >= 2 for a in totals.values())
        packet = dict(id=case['id'], triangulation=raw, coordinates=coordinates,
            parallelity=p['certificate'], boundary=b['certificate'],
            source_forest=tree, original_row_ids=ids, problem=problem, result=result)
        name = case['id'].replace('/', '__')+'.json'
        (args.output/name).write_text(json.dumps(json_safe(packet), indent=2)+'\n')
        record = dict(id=case['id'], packet=name, witness_rows=witness,
            witness_original_rows=[ids[r] for r in witness],
            witness_size=len(witness), every_witness_row_annular=True,
            witness_column_totals={str(c):a for c,a in sorted(totals.items())},
            source_and_boundary_authenticated=True, independently_reconstructed_matrix=True,
            negative_graph_certificate_verified=True)
        records.append(record)
        print(json.dumps(record), flush=True)
    assert len(records) == 3
    (args.output/'obstruction_audit.json').write_text(json.dumps(dict(cases=records,
        scope='No dual forest can make this fixed raw finite boundary kernel completely eliminable; no non-handlebody conclusion.'), indent=2)+'\n')


if __name__ == '__main__':
    main()
