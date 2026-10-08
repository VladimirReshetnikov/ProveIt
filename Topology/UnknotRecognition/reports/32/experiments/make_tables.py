import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
g=json.loads((ROOT/'results'/'growth.json').read_text())['results']
lines=[r'\begin{tabular}{lrrrrrr}',r'\toprule',r'Family & $n$ & Peak allocated & Peak minimal & Peak $\mu$ & Updates & $\dim\Kh$\\',r'\midrule']
for r in g:
 if r['status']!='COMPLETE': continue
 t=r['trace']; name=r['name'].replace('_',r'\_')
 lines.append(f"{name} & {r['crossings']} & {max(x['pre_objects'] for x in t)} & {max(x['objects'] for x in t)} & {max(x['occupancy'] for x in t)} & {sum(x['update_pairs'] for x in t)} & {r['rank']}\\\\")
lines += [r'\bottomrule',r'\end{tabular}']
(ROOT/'article'/'growth_table.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{llrrrr}',r'\toprule',r'Run & Torus crossings & Local (s) & Rebuild (s) & Paired ratio & A/A ratio\\',r'\midrule']
for run,file in [('A','benchmark.json'),('B','benchmark_retry_completed.json')]:
 for r in json.loads((ROOT/'results'/file).read_text())['results']:
  lines.append(f"{run} & {r['crossings']} & {r['local_median']:.4f} & {r['rebuild_median']:.4f} & {r['paired_median_ratio']:.3f} & {r['aa_median_ratio']:.3f}\\\\")
lines += [r'\bottomrule',r'\end{tabular}']
(ROOT/'article'/'timing_table.tex').write_text('\n'.join(lines)+'\n')
