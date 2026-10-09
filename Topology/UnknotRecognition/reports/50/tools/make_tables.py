"""Regenerate article tables from the retained measurements."""
from bootstrap import bootstrap
ROOT=bootstrap()
import json,statistics
p=ROOT/'paper/tables';p.mkdir(exist_ok=True)
x=json.loads((ROOT/'results/benchmark.json').read_text())
labels={'static-disjoint-6':'Disjoint, $r=6$','static-disjoint-8':'Disjoint, $r=8$',
        'static-disjoint-10':'Disjoint, $r=10$','coincident-4':'Coincident, $r=4$',
        'coincident-10':'Coincident, $r=10$','nested-10':'Nested, $r=10$',
        'paired-blocks-8':'Paired blocks, $r=8$','all-signatures-6':'All signatures, $r=6$'}
lines=[r'\begin{tabular}{@{}lrrrrr@{}}',r'\toprule',
       r'Workload & $s$ & Dense & Linear & Split & Split + replay\\',r'\midrule']
for c in x['cases']:
 m=c['medians_ms'];lines.append(labels[c['name']]+' & '+str(c['s'])+' & '+ ' & '.join(f'{m[a]:.3f}' for a in ['dense','linear','split','split_certified'])+r'\\')
lines += [r'\bottomrule',r'\end{tabular}']
(p/'timings.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{@{}lrrrr@{}}',r'\toprule',r'Workload & Dense queries & Split queries & Dense bytes & Sparse bytes\\',r'\midrule']
for c in x['cases']:
 lines.append(labels[c['name']]+' & '+str(c['stats']['dense']['orbit_queries'])+' & '+str(c['stats']['split']['orbit_queries'])+' & '+f"{c['certificate_bytes']['dense']:,}"+' & '+f"{c['certificate_bytes']['split_certified']:,}"+r'\\')
lines += [r'\bottomrule',r'\end{tabular}'];(p/'queries.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{@{}rrrrr@{}}',r'\toprule',r'$r$ & $s$ & Count queries & Query + replay (ms) & Certificate bytes\\',r'\midrule']
for c in x['large_cases']:
 lines.append(f"{c['r']} & {c['s']} & {c['stats']['orbit_queries']} & {c['median_ms']:.3f} & {c['certificate_bytes']:,}"+r'\\')
lines +=[r'\bottomrule',r'\end{tabular}'];(p/'large.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{@{}rrrrrr@{}}',r'\toprule',r'$r$ & $s$ & Cover: two searches & Cover: reuse & Two searches (ms) & Reuse (ms)\\',r'\midrule']
for c in x['signed_cases']:
 lines.append(f"{c['r']} & {c['s']} & {c['stats']['two_searches']['cover_orbit_queries']} & {c['stats']['support_reuse']['cover_orbit_queries']} & {c['median_ms']['two_searches']:.3f} & {c['median_ms']['support_reuse']:.3f}"+r'\\')
lines +=[r'\bottomrule',r'\end{tabular}'];(p/'signed.tex').write_text('\n'.join(lines)+'\n')
y=json.loads((ROOT/'results/benchmark_followup.json').read_text())
lines=[r'\begin{tabular}{@{}lrrrr@{}}',r'\toprule',r'Workload & Dense (ms) & Split (ms) & Paired gain & Split/control\\',r'\midrule']
for c in y['cases']:
 ctrl=statistics.median(a/b for a,b in zip(c['samples_ms']['split'],c['samples_ms']['split_control']))
 lines.append(labels[c['name']]+f" & {c['medians_ms']['dense']:.3f} & {c['medians_ms']['split']:.3f} & {c['paired_dense_over_arm']['split']:.2f} & {ctrl:.3f}"+r'\\')
lines +=[r'\bottomrule',r'\end{tabular}'];(p/'followup.tex').write_text('\n'.join(lines)+'\n')
print('Five tables regenerated from retained JSON.')
