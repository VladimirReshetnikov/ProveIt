"""Regenerate article tables from the retained raw samples; no timing rerun."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / 'results/benchmarks.json').read_text())
paired = [x for x in data['cases'] if x['scope'] == 'paired']
lines = [r'\begin{tabular}{lrrrrr}',r'\toprule',
         r'Workload & $s$ & Dense A (ms) & Dense B (ms) & Split (ms) & Paired ratio\\',
         r'\midrule']
for x in paired:
    m=x['median_ms'];ratio=x['paired_ratios']['split']
    lines.append(f"{x['name']} & {x['support']} & {m['dense-A']:.3f} & {m['dense-B']:.3f} & {m['split']:.3f} & {ratio:.2f}\\\\")
lines += [r'\bottomrule',r'\end{tabular}']
(ROOT/'article/timings.tex').write_text('\n'.join(lines)+'\n')
lines = [r'\begin{tabular}{lrrrr}',r'\toprule',
         r'Workload & Dense calls & Split calls & Split requests & Linear requests\\',r'\midrule']
for x in paired:
    samples=x['samples']
    a=next(v for v in samples if v['arm']=='dense-A' and v['round']==0)
    b=next(v for v in samples if v['arm']=='split' and v['round']==0)
    c=next(v for v in samples if v['arm']=='linear' and v['round']==0)
    lines.append(f"{x['name']} & {a['orbit_calls']} & {b['orbit_calls']} & {b['zeta_requests']} & {c['zeta_requests']}\\\\")
lines += [r'\bottomrule',r'\end{tabular}']
(ROOT/'article/query_counts.tex').write_text('\n'.join(lines)+'\n')
lines = [r'\begin{tabular}{rrrrr}',r'\toprule',
         r'Ports $r$ & Endpoint bits & Support $s$ & Orbit calls & Median (ms)\\',r'\midrule']
for x in data['cases']:
    if x['scope']!='capacity': continue
    row=next(v for v in x['samples'] if v['round']==0)
    lines.append(f"{x['ports']} & {x['input_size_bits']} & {x['support']} & {row['orbit_calls']} & {x['median_ms']['split']:.3f}\\\\")
lines += [r'\bottomrule',r'\end{tabular}']
(ROOT/'article/capacity.tex').write_text('\n'.join(lines)+'\n')
print('Generated three article tables from results/benchmarks.json')
