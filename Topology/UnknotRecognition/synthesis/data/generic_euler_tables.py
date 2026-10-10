"""Complete diagram recognition and supplied-sector query timings."""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'data/generic-euler-benchmark.json').read_text())
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
    (ROOT/'tables'/f'generic_euler_{group}.tex').write_text('\n'.join(lines)+'\n')

sector=json.loads((ROOT/'data/generic-euler-sector-benchmark.json').read_text())
lines=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
    r'Source & previous ms & current ms & old/new & old A/A & new A/A\\',r'\midrule']
for row in sector['cases']:
    cells=[r'\code{'+row['name'].replace('_',r'\_')+'}']+[f"{1000*row['medians'][a]:.3f}"for a in ('old','new')]
    cells += [f"{row['paired_ratios'][a]['median']:.3f}"for a in ('old_new','old_AA','new_AA')]
    lines.append(' & '.join(cells)+r'\\')
lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
(ROOT/'tables/generic_euler_sectors.tex').write_text('\n'.join(lines)+'\n')
