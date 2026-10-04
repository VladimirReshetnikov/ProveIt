#!/usr/bin/env python3
"""Regenerate the report's LaTeX tables from the retained raw benchmark JSON."""
from collections import defaultdict
import json
from pathlib import Path
from statistics import median
ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'results/benchmarks.json').read_text())
groups=defaultdict(list)
for row in data['observations']: groups[row['case'],row['variant']].append(row)
def m(case,variant):return median(r['seconds'] for r in groups[case,variant])
def val(case,variant):return groups[case,variant][0]
def comparison(cases,caption,label,milliseconds=False):
    multiplier=1000 if milliseconds else 1
    units='ms' if milliseconds else 's'
    s=[r'\begin{table}[H]\centering\small',r'\begin{tabular}{@{}lrrr@{}}\toprule',
       'Case & Baseline ('+units+') & Optimized ('+units+r') & Ratio \\\midrule']
    for case,title in cases:
        b,o=m(case,'baseline'),m(case,'optimized')
        if val(case,'baseline')['status']=='UNKNOWN':
            old=r'$>60$ (limited)';ratio=r'$>60/'+f'{o:.3f}'+r'$'
        else:
            old=f'{b*multiplier:.3f}' if milliseconds else f'{b:.6f}'
            ratio=f'{b/o:.2f}'+r'$\times$'
        new=f'{o*multiplier:.3f}' if milliseconds else f'{o:.6f}'
        s.append(f'{title} & {old} & {new} & {ratio} '+r'\\')
    s += [r'\bottomrule\end{tabular}',r'\caption{'+caption+r'}\label{'+label+r'}',r'\end{table}']
    return '\n'.join(s)
pipeline=[('pipeline/'+name,title) for name,title in [
    ('conway','Conway'),('kinoshita_terasaka','Kinoshita--Terasaka'),
    ('hard_unknot_8','Hard 8-crossing unknot'),('figure_eight','Figure-eight'),
    ('grid_determinant_one_knot','Grid determinant-one knot'),
    ('grid_scrambled_unknot','Scrambled grid unknot'),('torus_3_5','$T(3,5)$'),
    ('trefoil','Trefoil'),('unknot','Crossing-free unknot'),('unknot_braid40','40-crossing braid unknot')]]
rank=[('rank/'+name,title) for name,title in [
    ('conway','Conway, $n=11$'),('kinoshita_terasaka','Kinoshita--Terasaka, $n=11$'),
    ('hard_unknot_8','Hard unknot, $n=8$'),('torus_3_5','$T(3,5)$, $n=10$'),
    ('torus_3_11','$T(3,11)$, $n=22$'),('unknot_braid40','Braid unknot, $n=40$'),
    ('random_3_40','Random 3-braid, $n=40$'),('random_4_41','Random 4-braid, $n=41$'),
    ('random_5_36','Random 5-braid, $n=36$')]]
texts=[comparison(pipeline,'Full recognition pipeline on every supplied example. Ratios below one are regressions. Medians of three fresh-process API timings; milliseconds exclude Python startup.','tab:pipeline',True),
       comparison(rank,'Exact rank backend without Reidemeister preprocessing or invariant filters. Medians of three runs, except the one censored baseline stress run. A limited run is not a completed timing.','tab:rank')]
s=[r'\begin{table}[H]\centering\small',r'\begin{tabular}{@{}rrrrr@{}}\toprule',
   r'Trefoil factors & Crossings & Reduced rank & Baseline (s) & Optimized (s) \\\midrule']
for k in (2,4,6,8,16,32):
    case=f'factor/trefoils_{k}';b=f"{m(case,'baseline'):.6f}" if k<=8 else 'not run'
    s.append(f'{k} & {3*k} & {3**k:,} & {b} & '+f"{m(case,'optimized'):.6f}"+r'\\')
s += [r'\bottomrule\end{tabular}',r'\caption{Visible connected sums, rank backend only. The optimized computation scans one normalized trefoil factor and reuses it; all other work, including decomposition and degree convolution, is timed.}\label{tab:factors}\end{table}']
texts.append('\n'.join(s))
s=[r'\begin{table}[H]\centering\small',r'\begin{tabular}{@{}rrrrr@{}}\toprule',
   r'Tail $t$ & Runs & Time (s) & Peak generators & Peak RSS (MiB) \\\midrule']
for t,v in ((2,'optimized'),(3,'tail3'),(4,'tail4')):
    rows=groups['rank/random_5_36',v]
    s.append(f'{t} & {len(rows)} & {m("rank/random_5_36",v):.6f} & '+
             f"{max(r['stats']['max_objects_before_elimination'] for r in rows):,} & "+
             f"{max(r['peak_rss_kib'] for r in rows)/1024:.1f}"+r'\\')
s += [r'\bottomrule\end{tabular}',r'\caption{Tail trade-off on the 36-crossing stress case. Times are medians (one run for $t=4$); RSS is the maximum process high-water mark across the runs and includes runtime overhead. Every run returns reduced rank 2,949 and the same degree dimensions.}\label{tab:tails}\end{table}']
texts.append('\n'.join(s))
(ROOT/'docs/benchmark_tables.tex').write_text('\n\n'.join(texts)+'\n')
print('Generated benchmark tables from',len(data['observations']),'observations.')
