"""Regenerate report benchmark tables and numeric summary macros from raw data."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'results'/'benchmark.json').read_text())
fixed=[r for r in data['rows'] if r['kind']=='fixed-complex']
braids=[r for r in data['rows'] if r['kind']=='braid-scan']
fixed_names=['Gauge, $k=3$','Gauge, $k=3$','Gauge, $k=4$','Gauge, $k=3$','Sharp zigzag, $k=8$']
braid_names=[r'$\sigma_1^{25}$',r'$(\sigma_1\sigma_2)^6$',r'$(\sigma_1\sigma_2^{-1})^6$','Braid-relator unknot']
for filename,rows,names,head in [('benchmark_fixed.tex',fixed,fixed_names,'Fixed complex'),
                                ('benchmark_braids.tex',braids,braid_names,'Braid word')]:
    lines=[r'\begin{center}\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
           head+r' & $M$ & $R$ & Transfer (ms) & Pivot (ms) & Ratio\\\midrule']
    for r,name in zip(rows,names):
        m=r['median_seconds']
        lines.append(f"{name} & {r['M']} & {r['R']} & {1000*m['transfer']:.3f} & {1000*m['pivot']:.3f} & {r['pivot_over_transfer']:.2f}"+r'\\')
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'article'/filename).write_text('\n'.join(lines)+'\n')
profiles=[1000*r['median_seconds']['profile'] for r in fixed]
gain=next(r['pivot_over_transfer'] for r in braids if r['name']=='alternating-3-12')
macros={'BraidGain':f'{gain:.2f}','ProfileLow':f'{min(profiles):.3f}',
        'ProfileHigh':f'{max(profiles):.3f}'}
(ROOT/'article'/'results_macros.tex').write_text('\n'.join(
    '\\newcommand{\\'+k+'}{'+v+'}' for k,v in macros.items())+'\n')
