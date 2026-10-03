#!/usr/bin/env python3
"""Generate vector rule and simulated-orbit figures in an external directory."""
from pathlib import Path
import argparse, importlib.util, json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).resolve().parent.parent
spec=importlib.util.spec_from_file_location('component_rule',ROOT/'scientific/code/component_rule.py')
ca=importlib.util.module_from_spec(spec); spec.loader.exec_module(ca)
p=argparse.ArgumentParser(); p.add_argument('--output-dir',required=True,type=Path); args=p.parse_args()
out=args.output_dir.resolve()
if out==ROOT or ROOT in out.parents: raise RuntimeError('Figure output must be outside the release')
out.mkdir(parents=True,exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'pdf.fonttype':42})
colors=['#225c88','#ab4b32','#29806c','#885f9a']
meta={'Creator':'Report31 reproducible figures','CreationDate':None,'ModDate':None}
fig,axs=plt.subplots(2,2,figsize=(9.1,4.7),layout='constrained')
for ax,(name,(old,new)),color in zip(axs.flat,zip(['E   Adjacent pair moves east','W   Gap two pair moves west','R   Right marker lifts','L   Whole triple lifts'],ca.RULES.items()),colors):
 for y in [0,1]: ax.scatter(range(-1,6),[y]*7,color='#dddddd',s=10,zorder=0)
 old=sorted(old); new=sorted(new)
 for (x,y),(u,v) in zip(old,new):
  if (x,y)!=(u,v): ax.annotate('',xy=(u,v),xytext=(x,y),arrowprops={'arrowstyle':'->','lw':1.6,'color':color,'shrinkA':7,'shrinkB':7})
 ax.scatter(*zip(*old),s=90,facecolors='white',edgecolors='#222222',linewidths=1.4,zorder=3,label='input')
 ax.scatter(*zip(*new),s=32,color=color,zorder=4,label='output')
 ax.set(xlim=(-1.5,5.5),ylim=(-.6,1.6),xticks=range(-1,6),yticks=[0,1],title=name)
 ax.set_aspect('equal'); ax.spines[['top','right']].set_visible(False)
axs[0,0].legend(loc='upper right',frameon=False,ncol=2,fontsize=8)
fig.savefig(out/'rule.pdf',metadata=meta); plt.close(fig)
k=7; state=ca.initial(k); union=set()
for t in range(ca.section_time(k,8)+1):
 union |= state; state=ca.step(state)
points=sorted((x,y) for x,y in union if y<8)
# Carry particle identities through exactly the bijection used in the proof.
positions=[(0,0),(3,0),(4,0),(7,0)]; traces=[[] for _ in positions]
for t in range(97):
 for i,(x,y) in enumerate(positions): traces[i].append((x,y+t))
 mapping={}
 for component in ca.components(set(positions)):
  ax=min(x for x,y in component); ay=min(y for x,y in component)
  normalized=tuple(sorted((x-ax,y-ay) for x,y in component))
  replacement=ca.RULES.get(normalized,normalized)
  mapping.update({(x+ax,y+ay):(u+ax,v+ay) for (x,y),(u,v) in zip(normalized,sorted(replacement))})
 nxt=[mapping[p] for p in positions]
 if set(nxt)!=ca.step(set(positions)): raise RuntimeError('Matching disagrees with simulator')
 positions=nxt
fig,(a,b)=plt.subplots(1,2,figsize=(9.3,5.1),gridspec_kw={'width_ratios':[1.45,1]},layout='constrained')
a.scatter(*zip(*points),s=24,color=colors[0],label='visited')
holes=[(1,n) for n in range(8)]+[(k+n-1,n) for n in range(8)]
a.scatter(*zip(*holes),s=32,facecolors='none',edgecolors=colors[1],linewidths=1,label='two missing lines')
a.set(xlabel='horizontal coordinate x',ylabel='row n',title='G   First eight complete rows',xticks=range(0,15,2),yticks=range(8),xlim=(-.7,14.7),ylim=(-.7,7.7))
a.set_aspect('equal');a.legend(frameon=False,loc='upper center',bbox_to_anchor=(.5,-.16),ncol=2,fontsize=8)
for trace,color,label in zip(traces,colors,['left marker','moving particle 1','moving particle 2','right marker']):
 b.scatter(*zip(*trace),s=8,color=color,label=label)
b.set(xlabel='horizontal coordinate x',ylabel='height y',title='F   Four drifted traces',xticks=range(0,17,4),ylim=(-2,107));b.legend(frameon=False,loc='upper center',bbox_to_anchor=(.5,-.16),ncol=2,fontsize=7)
for ax in (a,b): ax.spines[['top','right']].set_visible(False);ax.grid(alpha=.12);ax.set_axisbelow(True)
fig.savefig(out/'orbits.pdf',metadata=meta);plt.close(fig)
(out/'simulation-data.json').write_text(json.dumps({'k':k,'G_complete_rows':8,'G_visited_points':points,'F_last_time':96,'F_traces':traces},sort_keys=True,indent=2)+'\n')
print(json.dumps({'status':'PASS','G_points':len(points),'F_points':sum(map(len,traces)),'figures':['rule.pdf','orbits.pdf']},sort_keys=True))
