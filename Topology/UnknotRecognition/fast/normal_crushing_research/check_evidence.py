"""Replay saved crushing evidence and arithmetic without discovery or Regina."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
from statistics import median

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import verify_crushing_recognition
from .fixtures import ROOT


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publication', action='store_true')
    args = parser.parse_args()
    data = ROOT/'synthesis/data'
    records = [json.loads((data/f'normal-crushing-{name}.json').read_text())
               for name in ('audit', 'benchmark', 'probe')]
    for record in records:
        assert record['passed']
        for name, expected in record['source_sha256'].items():
            assert digest(ROOT/name) == expected, name
    audit, benchmark, probe = records
    cases = audit['retained'] + audit['expanded'] + [audit['isolated_cycle']]
    cases += audit['one_tetrahedron']
    for chain in audit['diagram']['cases']:
        assert verify_crushing_chain(Diagram.from_pd([]), chain['certificate'])
        cases += chain['comparisons']
    counts = Counter()
    for case in cases:
        counts[case['status']] += 1
        if case['status'] == 'REJECTED':
            assert not case['oracle']['eligible']
            continue
        assert case['oracle']['eligible']
        packet = case['native']['certificate']
        assert verify_normal_crushing(case['source'], packet)
        for field in ('components', 'torus_component', 'successor'):
            assert packet[field] == case['oracle'][field]
        assert packet['triangulation'] == case['oracle']['quotient']
    assert counts == {'COMPLETE': 194, 'REJECTED': 5}, counts
    assert len(audit['retained']) == 18 and len(audit['expanded']) == 175
    for record in probe['records']:
        result = record['result']
        diagram = Diagram.from_pd(probe['input_pd'])
        if result['status'] == 'INCONCLUSIVE':
            assert verify_crushing_chain(diagram, result['partial_chain'])
        elif result['status'] in ('UNKNOT', 'KNOTTED'):
            assert verify_crushing_recognition(diagram, result['certificate'])
        else:
            assert result['status'] == 'CANCELLED'
    lines = [r'\begin{tabular}{lrrrrr}', r'\toprule',
             r'Case & Adaptive & Standard & Crush C & Crush D & A/A \\', r'\midrule']
    arms = ('adaptive', 'standard_ablation', 'crushing_canonical', 'crushing')
    for record in benchmark['records']:
        samples, aa = record['samples'], record['aa_samples']
        assert len(samples) == benchmark['pairs'] and len(aa) == benchmark['aa']
        for sample in samples:
            assert sorted(sample['order']) == sorted(arms)
            for arm in arms:
                assert sample['results'][arm]['output_sha256'] == record['warmup_sha256'][arm]
        for arm in arms:
            assert median(s['results'][arm]['ns'] for s in samples) == record['median_ns'][arm]
        for label, arm in (('adaptive', 'adaptive'), ('ablation', 'standard_ablation'),
                           ('canonical', 'crushing_canonical')):
            assert median(s['results'][arm]['ns']/s['results']['crushing']['ns']
                          for s in samples) == record[f'paired_{label}_over_crushing']
        for sample in aa:
            assert sorted(sample['order']) == ['A', 'B']
            assert all(v['output_sha256'] == record['warmup_sha256']['adaptive']
                       for v in sample['results'].values())
        assert median(s['results']['A']['ns']/s['results']['B']['ns']
                      for s in aa) == record['aa_ratio']
        name = record['id'].replace('_', r'\_')
        values = ' & '.join(f"{record['median_ns'][arm]/1e6:.3f}" for arm in arms)
        lines.append(f"{name} & {values} & {record['aa_ratio']:.3f} "+r'\\')
    lines += [r'\bottomrule', r'\end{tabular}']
    (data/'normal-crushing-table.tex').write_text('\n'.join(lines)+'\n')
    if args.publication:
        paths = {ROOT/name for record in records for name in record['source_sha256']}
        paths.update(Path(__file__).parent.glob('*'))
        paths.update((ROOT/'fast/tests').glob('test_normal_crushing*.py'))
        paths.update(data.glob('normal-crushing-*'))
        paths.update(ROOT/'synthesis'/name for name in (
            'normal_crushing_search.tex', 'marked_cut_handlebodies.tex', 'report.pdf'))
        paths.add(ROOT/'fast/README.md')
        target = data/'normal-crushing-publication.json'
        result = dict(passed=True, counts=dict(counts), source_authenticated_chains=2,
            general_quasipolynomial=False,
            source_sha256={str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)
                           if p.is_file() and p != target})
        target.write_text(json.dumps(result, indent=2)+'\n')
    print('PASS', dict(counts), 'two authenticated chains; timing and source pins checked')


if __name__ == '__main__':
    main()
