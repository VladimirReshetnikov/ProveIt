"""Independent original-equation replay; does not call either atlas backend."""
from collections import Counter
from hashlib import sha256
from itertools import product
import json
import statistics

from .common import ROOT, verify_vector
from .filtered_native import save
from .native import (matching, euler, sector_source, _prepare, build_sector_kernel, sector_rays)
from .check_evidence import canonical
from fastunknot.integer_codec import encoded_integer
from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate, normal_compressing_disk_count
from experiments.oracle import all_rays


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    data = ROOT/'synthesis/data'
    load = lambda name:json.loads((data/name).read_text())
    native = load('kernel-atlas-native.json')
    bench = load('kernel-atlas-benchmark.json')
    for record in (native, bench):
        assert record['passed']
        for name, expected in record['source_sha256'].items():
            assert digest(ROOT/name) == expected, name
    total = Counter()
    for case in native['records']:
        tri = case['triangulation']
        prepared = _prepare(tri, lambda: None)
        original = matching(tri)
        assert {canonical(r) for r in original.equations} == {
            canonical(tuple(r.get(j,0) for j in range(original.n))) for r in prepared['matching']}
        source, forbidden = sector_source(tri, case['support'])
        cost = euler(tri)
        if len(tri['tetrahedra']) == 2:
            rays = all_rays(original.n, original.equations, original.conflicts)
            rays = [r for r in rays if not any(r[j] for j in forbidden)]
        else:
            kernel = build_sector_kernel(tri, case['support'])
            rays = [tuple(v for row in rows for v in row) for rows in sector_rays(kernel)]
        accepted = []
        for r in rays:
            if sum(a*b for a,b in zip(cost,r)) <= 0:
                continue
            rows = [list(r[i:i+7]) for i in range(0, len(r), 7)]
            packet = normal_compressing_disk_count(tri, rows, record_certificate=True)
            assert packet['status']=='COMPLETE'
            assert verify_normal_disk_count_certificate(tri, rows, packet['certificate'])
            if packet['contains_compressing_disk']:
                accepted.append(r)
        for arm,result in case['results'].items():
            for a in result['answers']:
                z, answer = a['zeros'], a['result']
                found = any(not any(r[j] for j in z) for r in accepted)
                assert answer['status'] == ('ACCEPTED_EXTREME' if found else 'NO_ACCEPTED_EXTREME')
                assert found == bool(answer['trace'] and answer['trace'][-1]['evidence']['accepted'])
                previous = []
                for t,entry in enumerate(answer['trace']):
                    x = entry['coordinates']
                    assert verify_vector(source.n, source.equations, source.conflicts, cost, x,
                                         zeros=z, extreme=True)
                    support = frozenset(j for j,v in enumerate(x) if v)
                    if arm in ('filtered', 'kernel'):
                        assert all(not old<=support for old in previous)
                    evidence = entry['evidence']
                    assert type(evidence['accepted']) is bool
                    c = evidence['certificate']
                    assert c['coordinates']==x
                    rows = [x[i:i+7] for i in range(0,len(x),7)]
                    assert verify_normal_disk_count_certificate(tri,rows,c['disk_certificate'])
                    assert bool(encoded_integer(c['disk_certificate']['compressing_disk_components'])) == evidence['accepted']
                    assert c['contains_compressing_disk']==evidence['accepted']
                    if evidence['accepted']:
                        assert found and t==len(answer['trace'])-1
                    else:
                        previous.append(support)
                    total[arm+'_inspected'] += 1
                if arm in ('filtered', 'kernel'):
                    assert previous == list(map(frozenset,answer['rejected']))
                    assert answer['queries']==len(previous)+1
                    if arm == 'kernel':
                        total['queries'] += answer['queries']
                        total['rejections'] += len(previous)
                        total['transitions'] += answer['transitions']
                        total[answer['status']] += 1
    assert total['queries'] == total['rejections']+202
    assert total['ACCEPTED_EXTREME']==60 and total['NO_ACCEPTED_EXTREME']==142
    prior = load('port-subspace-native.json')
    restored = 0
    for old,new in zip(prior['records'],native['records']):
        assert old['id']==new['id']
        for a,b in zip(old['results']['intrinsic']['answers'],new['results']['kernel']['answers']):
            assert a['zeros']==b['zeros']
            was_disc = bool(a['certificate'] and a['certificate']['contains_compressing_disk'])
            now_disc = b['result']['status']=='ACCEPTED_EXTREME'
            assert not was_disc or now_disc
            restored += now_disc and not was_disc
    assert restored == 9
    lines = [r'\begin{tabular}{lrrrrr}',r'\toprule',
        r'Case & Native ms & Prior ms & Kernel ms & Kernel/Prior & A/A \\',r'\midrule']
    for r in bench['records']:
        assert len(r['samples'])==7 and len(r['duplicate_samples'])==3
        for arm in ('native','filtered','kernel'):
            assert r['warmup'][arm]['answers']==r['warmup']['native']['answers']
            assert statistics.median(s['arms'][arm]['ms'] for s in r['samples'])==r['median_ms'][arm]
            assert all(s['arms'][arm]['output_sha256']==r['warmup'][arm]['output_sha256'] for s in r['samples'])
        ratio = statistics.median(s['arms']['kernel']['ms']/s['arms']['filtered']['ms'] for s in r['samples'])
        ratio_native = statistics.median(s['arms']['kernel']['ms']/s['arms']['native']['ms'] for s in r['samples'])
        aa = statistics.median(s['a_ms']/s['b_ms'] for s in r['duplicate_samples'])
        assert ratio==r['paired_kernel_over_filtered'] and aa==r['duplicate_median_ratio']
        assert ratio_native==r['paired_kernel_over_native']
        name=r['id'].replace('_',r'\_')
        lines.append(f"{name} & {r['median_ms']['native']:.3f} & {r['median_ms']['filtered']:.3f} & {r['median_ms']['kernel']:.3f} & {ratio:.2f} & {aa:.3f} "+r'\\')
    lines += [r'\bottomrule',r'\end{tabular}']
    (data/'kernel-atlas-table.tex').write_text('\n'.join(lines)+'\n')
    files = sorted(data.glob('kernel-atlas-*'))
    files += sorted((ROOT/'fast/projective_port_research').glob('*.py'))
    files += [ROOT/'fast/fastunknot'/name for name in ('source_kernel.py','source_kernel_verify.py')]
    files += [ROOT/'synthesis/reusable_source_kernels.tex',ROOT/'synthesis/report.pdf']
    save(data/'kernel-atlas-publication.json',dict(passed=True,counts=dict(total),restored_discs=restored,
        native_cases=22, independent_whole_source_queries=112,
        no_atlas_discovery_used_for_replay=True,general_quasipolynomial=False,
        source_sha256={str(p.relative_to(ROOT)):digest(p) for p in files if p.name!='kernel-atlas-publication.json'}))
    print('PASS',dict(total),'restored discs',restored)


if __name__ == '__main__':
    main()
