"""Complete window queries with cached potential-mode projection."""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'data/euler-aggregate-benchmark.json').read_text())
for group in ('seed','recognition'):
    lines=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
        r'Input & previous ms & current ms & old/new & old A/A & new A/A\\',r'\midrule']
    for row in data['cases']:
        kind,name=row['name'].split('/')
        if kind!=group:continue
        cells=[name.replace('-',' ')]+[f"{1000*row['medians'][a]:.3f}"for a in ('old','new')]
        cells += [f"{row['paired_ratios'][a]['median']:.3f}"for a in ('old_new','old_AA','new_AA')]
        lines.append(' & '.join(cells)+r'\\')
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'tables'/f'euler_aggregate_{group}.tex').write_text('\n'.join(lines)+'\n')
