"""Regenerate binary prism-classification comparison timings."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
r=json.loads((ROOT/'data/cut-products-benchmark.json').read_text())
rows=[r'\begin{center}',r'\begin{tabular}{rrrrrrr}',r'\toprule',
      r'copies & expanded points & explicit ms & native ms & ratio & old A/A & new A/A\\',r'\midrule']
for case in r['cases']:
 n=int(case['name'].rsplit('-',1)[1]);m=case['medians'];p=case['paired_ratios']
 rows.append(f"{n} & {case['samples'][0]['measurements']['old']['expanded_points']} & {1000*m['old']:.3f} & {1000*m['new']:.3f} & {p['old_new']['median']:.3f} & {p['old_AA']['median']:.3f} & {p['new_AA']['median']:.3f}"+r'\\')
rows.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
(ROOT/'tables/cut_products_classification.tex').write_text('\n'.join(rows)+'\n')
