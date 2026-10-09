"""Regenerate article tables only from completed benchmark and audit files."""
from common import ROOT
from sparse_incidence.codec import load

x=load(ROOT/'results/benchmark.json')
labels={
 'static4000_coincident':'Static, coincident',
 'static4000_nested':'Static, nested',
 'static4000_disjoint':'Static, disjoint',
 'chain8_500_coincident':'8-block chain, coincident',
 'chain8_500_nested':'8-block chain, nested',
 'chain8_500_disjoint':'8-block chain, disjoint',
 'chain16_128_disjoint':'16-block chain, disjoint',
 'all_signatures_r5':'All 32 signatures',
 'small_mixed':'Small mixed relation'}
lines=[r'\begin{tabular}{@{}lrrrrr@{}}',r'\toprule',
       r'Workload & Dense & Flat & Balanced & Proof/replay & Ratio\\',r'\midrule']
for c in x['cases']:
 m=c['medians'];v=[m[a]*1000 for a in ('dense','flat','balanced','certified_replay')]
 lines.append(labels[c['name']]+' & '+' & '.join(f'{a:.3f}' for a in v)+
              f" & {c['paired_dense_over']['balanced']:.2f}"+r'\\')
lines += [r'\bottomrule',r'\end{tabular}']
(ROOT/'paper/timings.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{@{}lrrrrr@{}}',r'\toprule',
       r'Workload & $r$ & $s_0$ & Dense calls & Sparse calls & Proof KiB\\',r'\midrule']
for c in x['cases']:
 lines.append(labels[c['name']]+f" & {len(c['ports'])} & {c['support']} & "
  f"{c['stats']['dense']['orbit_calls']} & {c['stats']['balanced']['orbit_calls']} & "
  f"{c['certificate_bytes']/1024:.1f}"+r'\\')
lines += [r'\bottomrule',r'\end{tabular}']
(ROOT/'paper/queries.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{@{}lrrrrr@{}}',r'\toprule',
       r'Family & $r$ & Dense slots & Sparse rows & Calls & Time (ms)\\',r'\midrule']
for c in x['scaling']:
 name='Disjoint static' if c['name']=='disjoint_static' else 'One active port'
 lines.append(f"{name} & {c['rank']} & $2^{{{c['rank']}}}$ & {c['sparse_entries']} & "
              f"{c['stats']['orbit_calls']} & {1000*c['median']:.3f}"+r'\\')
lines += [r'\bottomrule',r'\end{tabular}']
(ROOT/'paper/scaling.tex').write_text('\n'.join(lines)+'\n')
