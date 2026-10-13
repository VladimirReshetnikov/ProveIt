"""Replay saved sector/diagram certificates and arithmetic, without discovery."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
from statistics import median

from fastunknot.diagram import Diagram
from fastunknot.normal_euler_verify import verify_sector_euler_certificate
from fastunknot.normal_sector_verify import verify_sector_exhaustion
from fastunknot.normal_crushing_verify import verify_normal_crushing
from .benchmark import ROOT, ARMS, encode_result, verify_result, load_baseline


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publication', action='store_true')
    args = parser.parse_args()
    data = ROOT/'synthesis/data'
    audit, benchmark, probe = [json.loads((data/f'euler-crushing-{name}.json').read_text())
                               for name in ('audit', 'benchmark', 'probe')]
    for record in (audit, benchmark, probe):
        assert record['passed']
        for name, expected in record['source_sha256'].items():
            assert digest(ROOT/name) == expected, name
    load_baseline()  # Verify the retained historical source pin; do not run it.
    counts = Counter()

    def replay_crush(source, record):
        proof = record['native']['certificate']
        assert verify_normal_crushing(source, proof)
        for native, oracle in (('triangulation', 'quotient'), ('components', 'components'),
                              ('torus_component', 'torus_component'), ('successor', 'successor')):
            assert proof[native] == record['regina'][oracle]
        counts['crushing_packets'] += 1

    for case in audit['records']:
        source, support = case['triangulation'], set(map(tuple, case['support']))
        oracle = audit['standard_vertex_oracles'][case['source_sha256']]
        assert oracle['triangulation'] == source
        target = [v['index'] for v in oracle['vertices'] if
                  v['euler_characteristic'] > 0 and not v['vertex_link'] and v['quad_support']
                  and all(tuple(q) in support for q in v['quad_support'])]
        assert target == case['oracle_positive_vertex_indices']
        assert bool(target) == case['oracle_positive']
        positive = case['oracle_positive']
        counts['positive_sectors' if positive else 'negative_sectors'] += 1
        if positive:
            replay_crush(source, case['corner']['crushing'])
        else:
            assert verify_sector_exhaustion(source, case['corner']['certificate'])
        for arm, result in case['results'].items():
            answer = result['result']
            assert (answer['status'] == 'POSITIVE_EULER') == positive
            assert verify_sector_euler_certificate(source, answer['certificate'])
            counts['euler_packets'] += 1
            if positive:
                assert result['extraction']['coordinates'] == result['crushing']['native']['certificate']['coordinates']
                replay_crush(source, result['crushing'])
    control = audit['nonextreme_control']
    replay_crush(control['triangulation'], control['crushing'])
    bad = deepcopy(control['crushing']['native']['certificate'])
    bad['coordinates'] = control['coordinates']
    assert not verify_normal_crushing(control['triangulation'], bad)
    assert counts == dict(positive_sectors=27, negative_sectors=11,
                          crushing_packets=82, euler_packets=76), counts
    assert audit['unique_sources'] == 5 and audit['original_standard_vertices'] == 86

    table = [r'\begin{tabular}{lrrrrr}', r'\toprule',
             r'Case & Adaptive & Sequential & Fair Q & Fair LP & A/A \\', r'\midrule']
    for record in benchmark['records']:
        diagram = Diagram.from_pd(record['input_pd'])
        for arm in ARMS:
            result = record['warmup_results'][arm]
            assert verify_result(diagram, result, arm) == 'recognition'
            assert sha256(encode_result(result)).hexdigest() == record['warmup_sha256'][arm]
            assert median(s['results'][arm]['ns'] for s in record['samples']) == record['median_ns'][arm]
        assert len(record['samples']) == benchmark['pairs']
        assert len(record['aa_samples']) == benchmark['aa']
        for sample in record['samples']:
            assert sorted(sample['order']) == sorted(ARMS)
            for arm in ARMS:
                assert sample['results'][arm]['output_sha256'] == record['warmup_sha256'][arm]
        for label, expected in record['paired_ratio'].items():
            left, right = label.split('_over_')
            assert median(s['results'][left]['ns']/s['results'][right]['ns']
                          for s in record['samples']) == expected
        for sample in record['aa_samples']:
            assert sorted(sample['order']) == ['A', 'B']
            assert all(v['output_sha256'] == record['warmup_sha256']['adaptive_disc']
                       for v in sample['results'].values())
        assert median(s['results']['A']['ns']/s['results']['B']['ns']
                      for s in record['aa_samples']) == record['aa_ratio']
        name = record['id'].replace('_', r'\_')
        values = ' & '.join(f"{record['median_ns'][arm]/1e6:.3f}" for arm in ARMS)
        table.append(f"{name} & {values} & {record['aa_ratio']:.3f} "+r'\\')
    table += [r'\bottomrule', r'\end{tabular}']
    (data/'euler-crushing-table.tex').write_text('\n'.join(table)+'\n')
    diagram = Diagram.from_pd(probe['input_pd'])
    for record in probe['records']:
        result = record['result']
        assert sha256(encode_result(result)).hexdigest() == record['output_sha256']
        if result['status'] == 'CANCELLED':
            assert record['independent_replay'] is None and not record['partial_result_returned']
        else:
            assert verify_result(diagram, result, record['arm']) == record['independent_replay']

    if args.publication:
        files = {ROOT/name for record in (audit, benchmark, probe)
                 for name in record['source_sha256']}
        files.update(data.glob('euler-crushing-*'))
        files.update((ROOT/'fast/tests').glob('test*euler*lp*.py'))
        files.update((ROOT/'fast/tests').glob('test*crushing*.py'))
        files.add(ROOT/'fast/tests/test_positive_ray.py')
        files.add(ROOT/'fast/README.md')
        files.update(ROOT/'synthesis'/name for name in (
            'euler_lp_crushing.tex', 'marked_cut_handlebodies.tex', 'report.pdf'))
        target = data/'euler-crushing-publication.json'
        output = dict(passed=True, counts=dict(counts), general_quasipolynomial=False,
            source_sha256={str(p.relative_to(ROOT)): digest(p) for p in sorted(files)
                           if p.is_file() and p != target})
        target.write_text(json.dumps(output, indent=2)+'\n')
    print('PASS', dict(counts), 'diagram evidence, timing arithmetic and source pins checked')


if __name__ == '__main__':
    main()
