"""Derive compact summaries and LaTeX tables from the final raw audit."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ARMS = ('pairwise','control','adaptive','joint')
d = json.loads((ROOT/'results.json').read_text())
summary = dict(query_counts={}, gordian={}, other_cases_summed_medians={},
               kernels=[], changed_adaptive_certificates=[], active_cases={})
for mode in ('explicit','compressed'):
    totals = {a:0 for a in ARMS}
    calls = {a:0 for a in ARMS}
    completed = count = 0
    active = []
    for row in d['rows']:
        q = row['modes'][mode]
        if row['name'] == 'gordian':
            summary['gordian'][mode] = {k:q[k] for k in ('completed_median_seconds','paired_ratios')}
        else:
            for a in ARMS:
                totals[a] += q['completed_median_seconds'][a] or 0
        if any(s['measurements']['adaptive']['overlap_queries'] for s in q['samples']):
            active.append(row['name'])
        for sample in q['samples']:
            count += len(sample['measurements'])
            for arm,res in sample['measurements'].items():
                completed += res['completed']
                calls[arm] += len(res['overlap_queries'])
            old = [g.get('certificate_sha256') for g in sample['measurements']['pairwise']['group_stages']]
            new = [g.get('certificate_sha256') for g in sample['measurements']['adaptive']['group_stages']]
            if old != new:
                summary['changed_adaptive_certificates'].append([row['name'],mode,old,new])
    summary['query_counts'][mode] = dict(measured=count,completed=completed,overlap_calls=calls)
    summary['other_cases_summed_medians'][mode] = totals
    summary['active_cases'][mode] = active
for row in d['kernels']:
    result = {k:row[k] for k in ('name','total_length','nonempty_relators','expected_gain',
                               'completed_median_seconds','paired_ratios')}
    result['first_sample_work'] = {a:row['samples'][0]['measurements'][a]['work'] for a in ARMS}
    result['adaptive_route'] = row['samples'][0]['measurements']['adaptive']['stats']['backend']
    summary['kernels'].append(result)
(ROOT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
lines = [r'\begin{table}[htbp]',r'\centering\small',
         r'\begin{tabular}{lrrrrr}',r'\toprule',
         r'Query & Pairwise & A/A & Adaptive & Joint only & Paired gain\\',r'\midrule']
for mode in ('explicit','compressed'):
    row = summary['gordian'][mode]
    values = row['completed_median_seconds']
    ratio = row['paired_ratios']['pairwise/adaptive']['median']
    name = 'Gordian, '+mode
    lines.append(name+' & '+' & '.join(f'{1000*values[a]:.2f}' for a in ARMS)+f' & ${ratio:.3f}\\times$'+r'\\')
for row in summary['kernels']:
    values, ratio = row['completed_median_seconds'], row['paired_ratios']['pairwise/adaptive']['median']
    name = {'gordian-derived':'Gordian overlap only','random-8x64':r'Synthetic $8\times64$',
            'random-32x64':r'Synthetic $32\times64$', 'random-128x64':r'Synthetic $128\times64$',
            'duplicate-periodic':'Synthetic periodic duplicates'}[row['name']]
    lines.append(name+' & '+' & '.join(f'{1000*values[a]:.2f}' for a in ARMS)+f' & ${ratio:.3f}\\times$'+r'\\')
lines += [r'\bottomrule',r'\end{tabular}',
          r'\caption{Final cyclic-overlap audit. Times are completed-query medians in milliseconds; paired gain is the median of within-round pairwise/adaptive ratios. Whole Gordian recognition includes fresh PD validation, all pipeline stages and independent replay (five measured rounds). Isolated exact queries include index construction and failed prelude work (three rounds). One warmup per arm is excluded. Synthetic rows are presentation-query workloads, not hard-knot recognition benchmarks.}',
          r'\label{tab:cyclic-overlap-audit}',r'\end{table}']
(ROOT/'table.tex').write_text('\n'.join(lines)+'\n')
print(json.dumps(summary,indent=2))
