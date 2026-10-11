"""Regenerate complete source-interface comparison timings."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
r=json.loads((ROOT/'data/prism-interfaces-benchmark.json').read_text())
rows=[r'\begin{center}',r'\begin{tabular}{lrrrrr}',r'\toprule',
      r'input & explicit ms & native ms & ratio & old A/A & new A/A\\',r'\midrule']
for case in r['cases']:
 parts=case['name'].split('-');label=f"$T={parts[1]}$, copies {parts[3]}"
 m=case['medians'];p=case['paired_ratios']
 rows.append(f"{label} & {1000*m['old']:.3f} & {1000*m['new']:.3f} & {p['old_new']['median']:.3f} & {p['old_AA']['median']:.3f} & {p['new_AA']['median']:.3f}"+r'\\')
rows.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
(ROOT/'tables/prism_interfaces_queries.tex').write_text('\n'.join(rows)+'\n')
