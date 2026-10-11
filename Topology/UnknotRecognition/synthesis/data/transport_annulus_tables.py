"""Explicit single-family and strict-epoch complete-call measurements."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'data/transport-annulus-benchmark.json').read_text())
for group in ('native','recognition'):
    lines=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
        r'Input & disc only ms & cap enabled ms & old/new & old A/A & new A/A\\',r'\midrule']
    for row in data['cases']:
        kind,name=row['name'].split('/')
        if kind!=group:continue
        cells=[name.replace('-',' ')]+[f"{1000*row['medians'][a]:.3f}"for a in ('old','new')]
        cells += [f"{row['paired_ratios'][a]['median']:.3f}"for a in ('old_new','old_AA','new_AA')]
        lines.append(' & '.join(cells)+r'\\')
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'tables'/f'transport_annulus_{group}.tex').write_text('\n'.join(lines)+'\n')
