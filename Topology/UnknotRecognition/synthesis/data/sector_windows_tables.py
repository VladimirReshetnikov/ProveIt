"""Separate native candidate queries from complete diagram recognition."""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'data/sector-windows-benchmark.json').read_text())
for group in ('seed','recognition'):
    lines=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
        r'Input & off ms & on ms & off/on & off A/A & on A/A\\',r'\midrule']
    for row in data['cases']:
        kind,name=row['name'].split('/')
        if kind!=group:continue
        cells=[name.replace('-',' ')]+[f"{1000*row['medians'][a]:.3f}"for a in ('old','new')]
        cells += [f"{row['paired_ratios'][a]['median']:.3f}"for a in ('old_new','old_AA','new_AA')]
        lines.append(' & '.join(cells)+r'\\')
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'tables'/f'sector_windows_{group}.tex').write_text('\n'.join(lines)+'\n')
