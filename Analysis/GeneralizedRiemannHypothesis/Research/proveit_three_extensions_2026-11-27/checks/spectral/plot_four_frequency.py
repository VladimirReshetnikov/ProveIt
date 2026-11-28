#!/usr/bin/env python3
"""Illustrate the rigorously certified m=3 optimizer; not part of the proof."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

here=Path(__file__).resolve().parent
cell=json.loads((here/'four_frequency_point_witnesses.json').read_text())['points']['3']
A,B,C,u,v,w,x=map(float,cell['z'])
s=np.array([x,u,v,w]);e=1/3
columns=np.vstack([np.cos((1+e)*s),np.sin((2+e)*s),np.cos((3+e)*s)])
weights=-np.array([(-1)**j*np.linalg.det(np.delete(columns,j,axis=1)) for j in range(4)])
weights/=weights.sum()
points=(np.pi/2-s/3)/(2*np.pi)
endpoint=points[0]
t=np.linspace(-endpoint,endpoint,4001)
theta=2*np.pi*t
f=np.cos(theta)+(A/3)*np.cos(4*theta)-(B/3)*np.cos(7*theta)-(C/3)*np.cos(10*theta)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,(ax,aw)=plt.subplots(2,1,figsize=(8.0,5.4),sharex=True,gridspec_kw={'height_ratios':[3,1.4]},layout='constrained')
ax.plot(t,f,color='#145d73',lw=2)
ax.axhline(0,color='#82949b',lw=.8)
allpoints=np.r_[-points,points]
ax.scatter(allpoints,np.zeros(8),s=24,color='#bb552b',zorder=4)
ax.set_ylabel('Critical polynomial')
ax.set_title(r'Four frequencies $\{1,4,7,10\}$: the exact critical interval',loc='left',fontsize=13,pad=12)
ax.text(.02,.94,'Supremal gap = 0.6314783916947718…',transform=ax.transAxes,va='top',fontsize=11,color='#233a46')
ax.set_ylim(-.07,3.1)
aw.vlines(np.r_[-points,points],0,np.r_[weights/2,weights/2],color='#bb552b',lw=2.5)
aw.scatter(np.r_[-points,points],np.r_[weights/2,weights/2],color='#bb552b',s=26)
aw.set_ylim(0,.36);aw.set_ylabel('Averaging mass');aw.set_xlabel('Circle coordinate $t$ (one period has length 1)')
aw.set_xlim(-.34,.34);aw.set_xticks(np.arange(-.3,.31,.1))
for a in (ax,aw):
    a.axvline(-endpoint,color='#82949b',lw=.8,ls='--');a.axvline(endpoint,color='#82949b',lw=.8,ls='--')
    a.grid(axis='y',alpha=.18)
fig.savefig(here/'four_frequency_m3.pdf')
fig.savefig(here/'four_frequency_m3.svg')
fig.savefig(here/'four_frequency_m3.png',dpi=150)
print(json.dumps({'cosine_coefficients':[1,A/3,-B/3,-C/3], 'positive_nodes':points.tolist(),'masses_per_node':(weights/2).tolist(),'gap':2*endpoint},indent=2))
