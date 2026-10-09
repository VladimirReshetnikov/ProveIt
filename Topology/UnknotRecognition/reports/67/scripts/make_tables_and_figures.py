"""Regenerate report tables and static figures from the frozen measurements."""
from pathlib import Path
import json
import statistics
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]
ARTICLE=ROOT/'article'
TABLES=ARTICLE/'tables'
FIGURES=ARTICLE/'figures'
TABLES.mkdir(exist_ok=True)
FIGURES.mkdir(exist_ok=True)
data=json.loads((ROOT/'results/controlled_benchmarks.json').read_text())
audit=json.loads((ROOT/'results/sector_euler_audit.json').read_text())

def row(items):
    return ' & '.join(map(str,items))+r' \\'+'\n'

labels={
 'fibonacci_lst_10':'Fibonacci layered torus',
 'cap_3_5_3':'Boundary-cap torus',
 'finite_trefoil':'Trefoil',
 'finite_trefoil_interior':'Trefoil, interior vertex',
 'finite_figureEight':'Figure-eight',
 'finite_figureEight_interior':'Figure-eight, interior vertex',
 'solid_torus_sum_rp3':r'Torus $\#\mathbb{RP}^3$',
 'solid_torus_sum_s2xs1':r'Torus $\#(S^2\!\times S^1)$',
}
text=[r'\begin{tabularx}{\textwidth}{@{}Xrrcrrrrr@{}}'+'\n',r'\toprule'+'\n',
      row(['Fixture','$t$','$d$','Sign','Old','LP','Replay','Env.','Replay']),r'\midrule'+'\n']
for r in data['sectors']:
    p,v=r['producer_seconds'],r['replay_seconds']
    text.append(row([labels[r['fixture_id']],r['tetrahedra'],r['matching_nullity'],
       '+' if r['status']=='POSITIVE_EULER' else '$-$',
       *[f'{x*1000:.2f}' for x in (p['old']['median'],p['anchors']['median'],v['anchors']['median'],p['envelope']['median'],v['envelope']['median'])]]))
text.extend([r'\bottomrule'+'\n',r'\end{tabularx}'+'\n'])
(TABLES/'sector_timings.tex').write_text(''.join(text))

text=[r'\begin{tabular}{@{}rrrrrrrr@{}}'+'\n',r'\toprule'+'\n',
 row(['$t$','Bits','Old build','Old replay','Ray build','Ray replay','Ratio','Ray bytes']),r'\midrule'+'\n']
for r in data['ray_paired']:
    p,v,c=r['producer_seconds'],r['replay_seconds'],r['combined_seconds']
    text.append(row([r['tetrahedra'],r['maximum_coordinate_bits'],
       *[f'{x*1000:.2f}' for x in (p['old']['median'],v['old']['median'],p['ray']['median'],v['ray']['median'])],
       f"{c['old']['median']/c['ray']['median']:.2f}",f"{r['certificate_bytes']['ray']:,}"]))
text.extend([r'\bottomrule'+'\n',r'\end{tabular}'+'\n'])
(TABLES/'ray_timings.tex').write_text(''.join(text))

text=[r'\begin{tabular}{@{}rrrrrr@{}}'+'\n',r'\toprule'+'\n',
 row(['$t$','Bits','Ray build (ms)','Replay (ms)','Rank operations','Proof bytes']),r'\midrule'+'\n']
for r in data['ray_scaling']:
    text.append(row([r['tetrahedra'],r['maximum_coordinate_bits'],
        f"{r['producer_seconds']['median']*1000:.2f}",f"{r['replay_seconds']['median']*1000:.2f}",
        f"{r['stats']['rank_operations']:,}",f"{r['certificate_bytes']:,}"]))
text.extend([r'\bottomrule'+'\n',r'\end{tabular}'+'\n'])
(TABLES/'ray_scaling.tex').write_text(''.join(text))

base=[r['tetrahedra'] for r in data['ray_paired']]
extra=[r['tetrahedra'] for r in data['ray_scaling']]
old=[r['combined_seconds']['old'] for r in data['ray_paired']]
new=[r['combined_seconds']['ray'] for r in data['ray_paired']]+[r['combined_seconds'] for r in data['ray_scaling']]
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,
                     'axes.labelcolor':'#17384C','text.color':'#17384C','axes.edgecolor':'#7A8C98',
                     'svg.fonttype':'none'})
fig,axes=plt.subplots(1,2,figsize=(7.2,3.2),layout='constrained')
colors={'old':'#B85D3F','ray':'#217D91'}
for name,xs,vals in [('General component proof',base,old),('Primitive ray proof',base+extra,new)]:
    c=colors['old' if xs==base else 'ray']
    axes[0].plot(xs,[r['median']*1000 for r in vals],marker='o',markersize=4,label=name,color=c,lw=1.7)
    axes[0].fill_between(xs,[r['minimum']*1000 for r in vals],[r['maximum']*1000 for r in vals],alpha=.12,color=c)
axes[0].set(xscale='log',yscale='log',xlabel='Tetrahedra',ylabel='Construction + replay (ms)',title='Complete certificate path')
axes[0].set_xticks([4,16,64,256,1024],[4,16,64,256,1024])
axes[0].legend(frameon=False,loc='upper left',fontsize=9)
axes[0].grid(axis='y',alpha=.15)
axes[1].plot(base,[r['certificate_bytes']['old'] for r in data['ray_paired']],marker='o',markersize=4,color=colors['old'],lw=1.7,label='General component proof')
axes[1].plot(base+extra,[r['certificate_bytes']['ray'] for r in data['ray_paired']]+[r['certificate_bytes'] for r in data['ray_scaling']],marker='o',markersize=4,color=colors['ray'],lw=1.7,label='Primitive ray proof')
axes[1].set(xscale='log',yscale='log',xlabel='Tetrahedra',ylabel='Compact JSON proof (bytes)',title='Serialized proof size')
axes[1].set_xticks([4,16,64,256,1024],[4,16,64,256,1024])
axes[1].grid(axis='y',alpha=.15)
for ext in ('pdf','svg','png'):
    fig.savefig(FIGURES/f'primitive_ray_performance.{ext}',dpi=190)
plt.close(fig)

summary=dict(
 sector_cases=len(data['sectors']),
 sector_geomean_old_over_anchors=statistics.geometric_mean([r['producer_seconds']['old']['median']/r['producer_seconds']['anchors']['median'] for r in data['sectors']]),
 sector_geomean_old_over_envelope=statistics.geometric_mean([r['producer_seconds']['old']['median']/r['producer_seconds']['envelope']['median'] for r in data['sectors']]),
 sector_aa_range=[min(r['producer_seconds']['old']['median']/r['producer_seconds']['old_copy']['median'] for r in data['sectors']),max(r['producer_seconds']['old']['median']/r['producer_seconds']['old_copy']['median'] for r in data['sectors'])],
 ray_aa_range=[min(r['combined_seconds']['old']['median']/r['combined_seconds']['old_copy']['median'] for r in data['ray_paired']),max(r['combined_seconds']['old']['median']/r['combined_seconds']['old_copy']['median'] for r in data['ray_paired'])],
 audit_old_producer_seconds=sum(r['exploratory_seconds']['old_screen'] for r in audit['records']),
 audit_anchor_producer_seconds=sum(r['exploratory_seconds']['new_producer'] for r in audit['records']),
 audit_anchor_replay_seconds=sum(r['exploratory_seconds']['new_independent_replay'] for r in audit['records']),
 audit_envelope_producer_seconds=sum(r['envelope']['exploratory_seconds']['producer'] for r in audit['records']),
 audit_envelope_replay_seconds=sum(r['envelope']['exploratory_seconds']['independent_replay'] for r in audit['records']),
)
(ROOT/'results/report_measurement_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
