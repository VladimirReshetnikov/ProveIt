"""Complete supplied-source discovery with independent proof replay."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
record=json.loads((ROOT/'data/matching-support-benchmark.json').read_text())
lines=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
    r'Source & previous ms & current ms & old/new & old A/A & new A/A\\',r'\midrule']
for row in record['cases']:
    label=row['name'].replace('_',r'\_')
    cells=[r'\code{'+label+'}']+[f"{1000*row['medians'][a]:.3f}"for a in ('old','new')]
    cells += [f"{row['paired_ratios'][a]['median']:.3f}"for a in ('old_new','old_AA','new_AA')]
    lines.append(' & '.join(cells)+r'\\')
lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
(ROOT/'tables/matching_support_queries.tex').write_text('\n'.join(lines)+'\n')
