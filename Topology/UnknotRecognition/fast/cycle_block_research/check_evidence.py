"""Check publication counts, source binding, saved plans, samples and snapshots."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import statistics
from native_audit import ROOT, cases
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles


def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    data=ROOT/'synthesis/data'
    native=json.loads((data/'cycle-block-native-audit.json').read_text())
    assert native['passed'] and len(native['records'])==126
    for name, sha in native['source_sha256'].items(): assert digest(ROOT/name)==sha,name
    assert sum(r['plan']['deferred_weight']==0 for r in native['records'])==124
    assert sum(r['delivered']['status']=='RESOURCE_LIMIT' for r in native['records'])==1
    # Reconstruct source counts, then replay the saved private order literally,
    # without calling either optimizer's plan checker.
    for case, row in zip(cases(),native['records']):
        assert case['id']==row['id']
        source=_prepare(case['triangulation'],lambda:None)
        geometry=_parallelity_geometry(source,_coordinates(source,case['coordinates'],lambda:None),lambda:None)
        reduced, proof=reduce_core_three_handles(geometry,strategy='max_weight')
        assert replay_core_three_handles(geometry,proof)==reduced
        counts={h['id']:dict(Counter(x['handle'] for x in h['cycle'] if x['dimension']==1)) for h in reduced['core']['handles2']}
        saved={int(r):{int(c):v for c,v in values.items()} for r,values in row['counts'].items()}
        assert counts==saved
        plan=row['plan'];live=set(plan['cancelled_rows']);used=set()
        for r,c in plan['cancellations']:
            assert r in live and c not in used and counts[r].get(c)==1
            assert all(not counts[s].get(c,0) for s in live-{r})
            live.remove(r);used.add(c)
        assert not live and len(used)==plan['matched_weight']
        assert set(plan['remaining_rows'])==set(counts)-set(plan['cancelled_rows'])
        assert len(plan['remaining_rows'])==plan['deferred_weight']==row['ordered']['deferred_weight']
        assert row['geometric_partial_cancellation'] is False
    for name in ('delivered','adapted'):
        a=json.loads((data/f'cycle-block-{name}-exhaustive.json').read_text())['exhaustive']
        assert (a['matrix_roles'],a['optimized_plans'],a['discrepancies'])==(31581,63162,0)
    for name, count in [('tests',50),('adapted-tests',50),('maintained-tests',10)]:
        log=(data/f'cycle-block-{name}.txt').read_text()
        assert f'Ran {count} tests' in log and log.endswith('OK\n')
    for stem,snapshot in [('native-before-prepass','before-prepass'),('native-audit-before-trial-cap','before-trial-cap')]:
        old=json.loads((data/f'cycle-block-{stem}.json').read_text())
        assert old['source_sha256']['fast/fastunknot/cycle_block_cancellation.py']==digest(data/f'cycle-block-{snapshot}.py')
    oldbench=json.loads((data/'cycle-block-benchmark-before-trial-cap.json').read_text())
    assert oldbench['source_sha256']['fast/fastunknot/cycle_block_cancellation.py']==digest(data/'cycle-block-before-trial-cap.py')
    bench=json.loads((data/'cycle-block-benchmark.json').read_text())
    prefix=json.loads((data/'cycle-block-prefix-benchmark.json').read_text())
    for report in (bench,prefix):
        for path, sha in report['source_sha256'].items():assert digest(ROOT/path)==sha,path
        for row in report['cases']:
            assert len(row['pairs'])==report['rounds'] and len(row['aa_samples_ns'])==3
            for mode, median in row['median_ms'].items():
                assert median==statistics.median(x['samples_ns'][mode] for x in row['pairs'])/1e6
    for row in prefix['cases']:
        s=row['columns']
        assert row['answers']['delivered']['stats']['kernel_assignments']==s*s+s+1
        assert row['answers']['maintained']['stats']['kernel_assignments']==2*s+1
    names=['Pachner mixed','nested links','loop links','cactus 128',r'$K_{2,48}$']
    table=[r'\begin{center}',r'\begin{tabular}{lrrrrr}',
           r'query & ordered ms & delivered ms & new ms & ordered/new & A/A\\',r'\hline']
    for name,row in zip(names,bench['cases']):
        med=row['median_ms']
        delivered=(f"{med['delivered']:.3f}" if row['answers']['delivered']['status']=='OPTIMAL_MATRIX_PLAN' else 'cap')
        if delivered=='cap':assert row['paired_delivered_over_maintained'] is None
        table.append(f"{name} & {med['ordered']:.3f} & {delivered} & {med['maintained']:.3f} & {row['paired_ordered_over_maintained']:.2f} & {row['aa_ratio']:.3f}"+r'\\')
    table += [r'\end{tabular}',r'\end{center}']
    (data/'cycle-block-benchmark-table.tex').write_text('\n'.join(table)+'\n')
    files=list(data.glob('cycle-block-*'))+[ROOT/'fast/fastunknot/cycle_block_cancellation.py',ROOT/'fast/tests/test_cycle_block_cancellation.py',ROOT/'synthesis/cycle_block_cancellation.tex',ROOT/'synthesis/report.pdf']
    files+=list(Path(__file__).parent.glob('*.py'))
    result=dict(passed=True,native_sources=126,private_plans=126,fully_peeled=124,
        schema_scope='Feasible private orders and source counts; no geometric partial successor.',
        source_sha256={str(p.relative_to(ROOT)):digest(p) for p in files if p.name!='cycle-block-publication.json'})
    (data/'cycle-block-publication.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: 126 source-bound plans; 124 full and two optimal single deferrals; samples and historical snapshots verified.')


if __name__=='__main__':main()
