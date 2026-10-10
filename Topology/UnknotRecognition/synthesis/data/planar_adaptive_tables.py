"""Scope-separated paired tables for adaptive discovery and kernel reuse."""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'data/planar-adaptive-benchmark.json').read_text())
tables={g:[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
    r'Input & old ms & new ms & old/new & old A/A & new A/A\\',r'\midrule']
    for g in ('discovery','controls','sparse')}
for row in data['cases']:
    group,name=row['name'].split('/')
    target='controls'if group in ('control','enumeration')else group
    if name.startswith('double-cap-'):label='Base '+name.split('-')[-1]
    elif name.startswith('single-cap-'):label='One cap '+name.split('-')[-1]
    elif name=='complete-negative':label='Complete negative'
    elif name=='empty-sector':label='Empty sector'
    else:label='Capped '+('trefoil'if 'trefoil'in name else 'figure eight')
    if group=='enumeration':label='Enumeration '+name.split('-')[-1]
    cells=[label]+[f"{1000*row['medians'][a]:.3f}"for a in ('old','new')]
    cells += [f"{row['paired_ratios'][a]['median']:.3f}"for a in ('old_new','old_AA','new_AA')]
    tables[target].append(' & '.join(cells)+r'\\')
for group,lines in tables.items():
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'tables'/f'planar_adaptive_{group}.tex').write_text('\n'.join(lines)+'\n')
