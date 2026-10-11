"""Regenerate complete-query paired matching timings."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
r=json.loads((ROOT/'data/matching-pairs-benchmark.json').read_text())
labels={'figure-eight-pair-0':'figure eight sector A','figure-eight-pair-1':'figure eight sector B',
        'existing-single-row':'existing reduction','no-pair-control':'unreduced control'}
rows=[r'\begin{center}',r'\begin{tabular}{lrrrrr}',r'\toprule',
      r'Source sector & single ms & pair ms & old/new & old A/A & new A/A\\',r'\midrule']
for case in r['cases']:
 m=case['medians'];p=case['paired_ratios']
 rows.append(f"{labels[case['name']]} & {1000*m['old']:.3f} & {1000*m['new']:.3f} & {p['old_new']['median']:.3f} & {p['old_AA']['median']:.3f} & {p['new_AA']['median']:.3f}"+r'\\')
rows.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
(ROOT/'tables/matching_pairs_queries.tex').write_text('\n'.join(rows)+'\n')
