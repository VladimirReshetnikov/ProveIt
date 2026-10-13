"""Replay saved vertex-reduction evidence without normal-surface discovery."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from statistics import median

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from .benchmark import ROOT, ARMS, encode_result, verify_result, load_baseline


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publication', action='store_true')
    args = parser.parse_args()
    data = ROOT/'synthesis/data'
    audit, benchmark, probe = [json.loads((data/f'vertex-reduction-{name}.json').read_text())
                               for name in ('audit', 'benchmark', 'probe')]
    for record in (audit, benchmark, probe):
        assert record['passed']
        for name, expected in record['source_sha256'].items():
            assert digest(ROOT/name) == expected, name
    load_baseline()
    counts = Counter()
    for record in audit['supplied']+[r for d in audit['diagrams'] for r in d['records']]:
        source, result = record['source'], record['native']
        assert sha256(encode_result(source)).hexdigest() == record['source_sha256']
        prepared = _prepare(source, lambda: None)
        assert prepared['vertices'] == record['oracle_vertices'] == result['stats']['vertex_count']
        counts[result['status']] += 1
        if result['status'] == 'ONE_VERTEX':
            assert prepared['vertices'] == 1 and result['coordinates'] is None
            continue
        assert result['status'] == 'POSITIVE_EULER' and prepared['vertices'] > 1
        raw, canonical = result['raw_coordinates'], result['canonical_coordinates']
        raw_info = _coordinates(prepared, raw, lambda: None)
        canonical_info = _coordinates(prepared, canonical, lambda: None)
        assert raw == record['regina']['raw_coordinates']
        assert raw_info['euler_characteristic'] == record['regina']['raw_euler'] == result['stats']['raw_euler']
        assert canonical_info['euler_characteristic'] == record['regina']['canonical_euler'] == result['stats']['canonical_euler'] > 0
        assert max(x for row in raw for x in row) <= 2
        assert sum(map(sum, raw)) <= 4*len(raw)
        minima = {}
        for c, vertex in enumerate(prepared['vertex_roots']):
            minima[vertex] = min(minima.get(vertex, raw[c//4][c%4]), raw[c//4][c%4])
        expected = [row[:] for row in raw]
        for c, vertex in enumerate(prepared['vertex_roots']):
            expected[c//4][c%4] -= minima[vertex]
        assert expected == canonical
        for key, rows in [('raw_components', raw), ('canonical_components', canonical)]:
            components = record['regina'][key]
            assert all(c['orientable'] and c['euler'] in (1, 2) and
                       c['boundary'] == (c['euler'] == 1) for c in components)
            assert [[sum(c['coordinates'][t][j] for c in components) for j in range(7)]
                    for t in range(len(rows))] == rows
        assert any(c['euler'] == 1 and not c['vertex_link'] for c in record['regina']['raw_components'])
        assert all(not c['vertex_link'] for c in record['regina']['canonical_components'])
        proof = record['crushing']['certificate']
        assert result['coordinates'] == proof['coordinates']
        assert verify_normal_crushing(source, proof)
        oracle = record['regina']['extracted_ray']
        for native, reference in [('triangulation', 'quotient'), ('components', 'components'),
                                  ('torus_component', 'torus_component'), ('successor', 'successor')]:
            assert proof[native] == oracle[reference]
        if 'standard_vertex_oracle' in record:
            vertices = record['standard_vertex_oracle']
            matches = [i for i, v in enumerate(vertices['vertices']) if v['coordinates'] == result['coordinates']]
            assert matches == [vertices['extracted_ray_index']]
        counts['regina_edge_link_equal'] += 1
        counts['regina_labelled_quotient_equal'] += 1
        counts['expanded_links'] += bool(result['diagnostics']['face_additions'])
        counts['peeled_links'] += bool(record['regina']['peeled_vertex_links'])
        counts['double_triangle'] += any(2 in row[:4] for row in raw)
        counts['double_quad'] += any(2 in row[4:] for row in raw)
        counts['repeated_seed_face'] += bool(record['regina']['repeated_seed_face_occurrences'])
        counts['fresh_standard_vertex_lists'] += 'standard_vertex_oracle' in record
    assert dict(counts) == audit['summary']
    for case in audit['diagrams']:
        chain = case['chain']
        assert verify_crushing_chain(Diagram.from_pd(case['input_pd']), chain)
        assert [r['crushing']['certificate'] for r in case['records']] == chain['steps']
        current = chain['shelling']['triangulation']
        for record in case['records']:
            assert record['source'] == current
            current = record['crushing']['certificate']['successor']
        assert current == chain['triangulation']
        if current is not None:
            assert _prepare(current, lambda: None)['vertices'] == case['successor_vertices'] == 1
            assert len(current['tetrahedra']) == case['successor_tetrahedra']
        else:
            assert case['preprocessing_status'] == 'UNKNOT' and case['successor_tetrahedra'] == 0

    table = [r'\begin{tabular}{lrrrrrr}', r'\toprule',
             r'Case & Adaptive & Prior Q & Prior LP & Vertex Q & Vertex LP & A/A \\', r'\midrule']
    for record in benchmark['records']:
        diagram = Diagram.from_pd(record['input_pd'])
        assert len(record['samples']) == benchmark['pairs']
        assert len(record['aa_samples']) == benchmark['aa']
        for arm in ARMS:
            assert verify_result(diagram, record['warmup_results'][arm], arm) == 'recognition'
            assert sha256(encode_result(record['warmup_results'][arm])).hexdigest() == record['warmup_sha256'][arm]
            assert median(s['results'][arm]['ns'] for s in record['samples']) == record['median_ns'][arm]
        for sample in record['samples']:
            assert sorted(sample['order']) == sorted(ARMS)
            for arm in ARMS:
                assert sample['results'][arm]['output_sha256'] == record['warmup_sha256'][arm]
        for label, ratio in record['paired_ratio'].items():
            left, right = label.split('_over_')
            assert median(s['results'][left]['ns']/s['results'][right]['ns'] for s in record['samples']) == ratio
        for sample in record['aa_samples']:
            assert sorted(sample['order']) == ['A', 'B']
            assert all(v['output_sha256'] == record['warmup_sha256']['adaptive_disc']
                       for v in sample['results'].values())
        assert median(s['results']['A']['ns']/s['results']['B']['ns'] for s in record['aa_samples']) == record['aa_ratio']
        name = record['id'].replace('_', r'\_')
        values = ' & '.join(f"{record['median_ns'][arm]/1e6:.3f}" for arm in ARMS)
        table.append(f"{name} & {values} & {record['aa_ratio']:.3f} "+r'\\')
    table += [r'\bottomrule', r'\end{tabular}']
    (data/'vertex-reduction-table.tex').write_text('\n'.join(table)+'\n')
    diagram = Diagram.from_pd(probe['input_pd'])
    for record in probe['records']:
        result = record['result']
        assert sha256(encode_result(result)).hexdigest() == record['output_sha256']
        if result['status'] == 'CANCELLED':
            assert record['independent_replay'] is None and not record['partial_result_returned']
        else:
            assert verify_result(diagram, result, record['arm']) == record['independent_replay']

    if args.publication:
        files = {ROOT/name for record in (audit, benchmark, probe) for name in record['source_sha256']}
        files.update(data.glob('vertex-reduction-*'))
        files.update((ROOT/'fast/tests').glob('test*crushing*.py'))
        files.add(ROOT/'fast/tests/test_normal_vertex_reduction.py')
        files.add(ROOT/'fast/README.md')
        files.update(ROOT/'synthesis'/name for name in ('vertex_reduction.tex', 'euler_lp_crushing.tex',
            'marked_cut_handlebodies.tex', 'report.pdf'))
        target = data/'vertex-reduction-publication.json'
        target.write_text(json.dumps(dict(passed=True, counts=dict(counts), polynomial_vertex_reduction=True,
            general_quasipolynomial=False, source_sha256={str(p.relative_to(ROOT)): digest(p)
            for p in sorted(files) if p.is_file() and p != target}), indent=2)+'\n')
    print('PASS', dict(counts), 'saved chains, timing arithmetic and source pins checked')


if __name__ == '__main__':
    main()
