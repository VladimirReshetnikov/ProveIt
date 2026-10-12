"""Check and summarize archived result claims without rerunning timings."""

from collections import Counter
from pathlib import Path
import json
import statistics


ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'research/data'
load = lambda name: json.loads((DATA / name).read_text())
baseline = load('baseline_audit.json')
bfs = load('dual_bfs_audit.json')
weighted = load('dual_max_audit.json')
oracle = load('regina_audit.json')
timings = load('core_dual_paired_timings.json')
assert len(baseline['records']) == len(bfs['records']) == len(weighted['records']) == 106
assert all(report['corpus_sha256'] == baseline['corpus_sha256']
           for report in (bfs, weighted, oracle))
new = []
comparable = 0
positive_open = []
negative_open = []
for old, a, b, ref in zip(baseline['records'], bfs['records'],
                          weighted['records'], oracle['records']):
    assert old['id'] == a['id'] == b['id'] == ref['id']
    assert a['status'] == b['status']
    if old['status'] == 'COMPLETE':
        assert b['status'] == 'COMPLETE' and old['histogram'] == b['histogram']
    if b['status'] == 'COMPLETE':
        assert a['replay'] and b['replay']
        assert a['histogram'] == b['histogram']
        if old['status'] != 'COMPLETE':
            new.append(dict(id=b['id'], histogram=b['histogram']))
        if ref['status'] == 'COMPLETE':
            assert ref['histogram'] == b['histogram']
            comparable += 1
    elif ref['status'] == 'COMPLETE':
        destination = negative_open if any(x['genus'] < 0 for x in ref['histogram']) else positive_open
        destination.append(b['id'])
interior = [c for c in timings['cases'] if not c['id'].startswith('no_three/')]
both = [c for c in interior if all(c['native'][s]['status'] == 'COMPLETE'
                                 for s in ('bfs', 'max_weight'))]
ratios = [statistics.median(x['max_weight']['total'] for x in c['samples']) /
          statistics.median(x['bfs']['total'] for x in c['samples']) for c in both]
selected = next(c for c in timings['cases'] if c['id'] == 'interior/mobius_512')
summary = dict(
    baseline_counts=baseline['counts'], weighted_counts=weighted['counts'],
    oracle_counts=oracle['counts'], preserved_baseline_successes=85,
    new_successes=new, direct_positive_oracle_comparisons=comparable,
    positive_inconclusive=positive_open, nonhandlebody_inconclusive=negative_open,
    extra_16_counts={s: sum(c['native'][s]['status'] == 'COMPLETE' for c in interior)
                     for s in ('disabled', 'bfs', 'max_weight')},
    median_time_ratios_max_over_bfs=dict(count=len(ratios), minimum=min(ratios),
                                       median=statistics.median(ratios), maximum=max(ratios)),
    mobius512=dict(normal_discs=selected['normal_discs'],
                   explicit_tetrahedra=selected['reference']['cut_tetrahedra'],
                   histogram=selected['reference']['histogram'],
                   max_weight_median_seconds=statistics.median(x['max_weight']['total'] for x in selected['samples']),
                   explicit_median_seconds=statistics.median(x['explicit'] for x in selected['samples']),
                   median_paired_explicit_over_weighted=statistics.median(x['explicit']/x['max_weight']['total'] for x in selected['samples'])))
assert (comparable, len(new), len(positive_open), len(negative_open)) == (85, 7, 8, 6)
output = DATA / 'results_summary.json'
output.write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k not in
                  ('new_successes', 'positive_inconclusive', 'nonhandlebody_inconclusive')}, indent=2))
