"""Replay retained source witnesses and rebuild tables without atlas discovery."""
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import statistics

from .common import ROOT, Block, verify_synchronized, verify_vector, save
from projective_ports.source import synchronized_source
from experiments.oracle import all_rays, positive
from .native import _prepare, _coordinates, matching, euler, sector_source
from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate
from fastunknot.integer_codec import encoded_integer


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def canonical(row):
    first = next((x for x in row if x), 1)
    return tuple(Q(x)/first for x in row)


def main():
    data = ROOT/'synthesis/data'
    load = lambda name:json.loads((data/name).read_text())
    random = load('port-subspace-audit.json')
    native = load('port-subspace-native.json')
    bench = load('port-subspace-benchmark.json')
    for report in (random, native, bench):
        assert report['passed']
        for path, expected in report['source_sha256'].items():
            assert digest(ROOT/path) == expected, path
    queries = certificates = 0
    for record in random['models']:
        blocks = tuple(Block(**b) for b in record['blocks'])
        source, _, offsets = synchronized_source(blocks, ((0,)*3,)*2)
        rays = all_rays(source.n, source.equations, source.conflicts)
        for row in record['queries']:
            _, cost, _ = synchronized_source(blocks, row['costs'], row['master'])
            zeros = tuple(off+j for off, zz in zip(offsets, row['zeros']) for j in zz)
            expected = bool(positive(rays, cost, zeros))
            assert row['expected'] == expected == (row['answer']['status']=='POSITIVE')
            queries += 1
            if expected:
                assert verify_synchronized(blocks, row['costs'], row['answer'],
                                            master=row['master'], zeros=row['zeros'])
                x = row['certificate']['coordinates']
                assert verify_vector(source.n, source.equations, source.conflicts, cost, x,
                                     zeros=zeros, extreme=True)
                assert tuple(x) in rays
                certificates += 1
    assert queries == random['queries'] == 2160
    assert certificates == random['positives'] == 768
    query_count = missed_discs = 0
    positive_counts, disc_counts = Counter(), Counter()
    oracle_cache = {}
    dimensions = Counter()
    for record in native['records']:
        tri = record['triangulation']
        prepared = _prepare(tri, lambda: None)
        original = matching(tri)
        # Exact agreement with independently reconstructed native matching rows.
        assert {canonical(row) for row in original.equations} == {
            canonical(tuple(row.get(i, 0) for i in range(original.n))) for row in prepared['matching']}
        source, forbidden = sector_source(tri, record['support'])
        cost = euler(tri)
        targets = [a['positive'] for a in record['results']['native']['answers']]
        native_discs = [bool(a['certificate'] and a['certificate']['contains_compressing_disk'])
                        for a in record['results']['native']['answers']]
        intrinsic_discs = [bool(a['certificate'] and a['certificate']['contains_compressing_disk'])
                           for a in record['results']['intrinsic']['answers']]
        assert all(not new or old for old, new in zip(native_discs, intrinsic_discs))
        missed_discs += sum(old and not new for old, new in zip(native_discs, intrinsic_discs))
        query_count += len(targets)
        dimensions[record['results']['intrinsic']['stats']['intrinsic_dimension']] += 1
        for arm, result in record['results'].items():
            assert [a['positive'] for a in result['answers']] == targets
            if record['independent_source_oracle']:
                key = json.dumps(tri, sort_keys=True)
                if key not in oracle_cache:
                    oracle_cache[key] = all_rays(original.n, original.equations, original.conflicts)
                assert [bool(positive(oracle_cache[key], cost, tuple(a['zeros'])+forbidden))
                        for a in result['answers']] == targets
            for a in result['answers']:
                if not a['positive']:
                    assert a['certificate'] is None
                    continue
                positive_counts[arm] += 1
                c = a['certificate']
                x = c['coordinates']
                assert verify_vector(source.n, source.equations, source.conflicts, cost, x,
                                     zeros=a['zeros'], extreme=True)
                rows = [x[i:i+7] for i in range(0, len(x), 7)]
                analysed = _coordinates(prepared, rows, lambda: None)
                assert analysed['euler_characteristic'] == sum(a*b for a,b in zip(cost,x))
                assert verify_normal_disk_count_certificate(tri, rows, c['disk_certificate'])
                assert isinstance(c['contains_compressing_disk'], bool)
                assert c['contains_compressing_disk'] == bool(encoded_integer(
                    c['disk_certificate']['compressing_disk_components']))
                disc_counts[arm] += c['contains_compressing_disk']
    assert query_count == 202 and dimensions == {1:4, 2:18}
    assert positive_counts == {'native':69, 'delivered':69, 'intrinsic':69}
    assert disc_counts == {'native':60, 'delivered':51, 'intrinsic':51}
    assert missed_discs == 9
    initial = load('port-subspace-initial-benchmark.json')
    assert not initial['passed']
    assert initial['source_sha256']['fast/projective_port_research/benchmark.py'] == digest(data/'port-subspace-initial-benchmark.py')
    assert 'AssertionError' in (data/'port-subspace-initial-benchmark.txt').read_text()
    lines = [r'\begin{tabular}{lrrrrr}', r'\toprule',
             r'Case & Native ms & Atlas ms & Intrinsic ms & Atlas/Intrinsic & A/A \\', r'\midrule']
    for r in bench['records']:
        assert len(r['samples']) == 7 and len(r['duplicate_samples']) == 3
        for arm in ('native', 'delivered', 'intrinsic'):
            median = statistics.median(s['arms'][arm]['ms'] for s in r['samples'])
            assert median == r['median_ms'][arm]
            assert all(s['arms'][arm]['output_sha256']==r['warmup'][arm]['output_sha256'] for s in r['samples'])
            if arm != 'intrinsic':
                ratio = statistics.median(s['arms'][arm]['ms']/s['arms']['intrinsic']['ms'] for s in r['samples'])
                assert ratio == r['paired_median_ratios'][arm]
        aa = statistics.median(s['a_ms']/s['b_ms'] for s in r['duplicate_samples'])
        assert aa == r['duplicate_median_ratio']
        m = r['median_ms']
        name = r['id'].replace('_', r'\_')
        lines.append(f"{name} & {m['native']:.3f} & {m['delivered']:.3f} & {m['intrinsic']:.3f} & {r['paired_median_ratios']['delivered']:.2f} & {aa:.3f} "+r'\\')
    lines += [r'\bottomrule', r'\end{tabular}']
    (data/'port-subspace-table.tex').write_text('\n'.join(lines)+'\n')
    files = sorted(data.glob('port-subspace-*'))+sorted(data.glob('port-atlas-delivered-*'))
    files += [ROOT/'synthesis/intrinsic_port_atlases.tex', ROOT/'synthesis/report.pdf']
    files += sorted((ROOT/'fast/fastunknot').glob('*.py'))
    files += sorted((ROOT/'fast/projective_port_research').glob('*.py'))
    output = dict(passed=True, algebra_queries=queries, algebra_positive_certificates=certificates,
        native_queries=query_count, native_positives=dict(positive_counts), native_discs=dict(disc_counts),
        intrinsic_dimensions=dict(dimensions), benchmark_cases=len(bench['records']),
        no_atlas_discovery_used_for_replay=True, general_quasipolynomial=False,
        source_sha256={str(p.relative_to(ROOT)):digest(p) for p in files
                       if p.name!='port-subspace-publication.json'})
    save(data/'port-subspace-publication.json', output)
    print('PASS', queries, 'algebra queries;', query_count, 'native queries;', dict(disc_counts))


if __name__ == '__main__':
    main()
