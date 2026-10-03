"""Optional figure rendering; requires matplotlib. Trace verification is standard-library only."""
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator
P=Path(__file__).resolve().parent
data=json.loads((P/'verified_trace.json').read_text())['small']
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'pdf.fonttype':42,'ps.fonttype':42})
fig=plt.figure(figsize=(7.1,5.6),layout='constrained')
gs=fig.add_gridspec(2,1,height_ratios=[3.4,1.35])
ax=fig.add_subplot(gs[0]);trace=data['trace'];colors=['#161616','#161616','#205b86','#205b86','#161616']
# Sort order does not carry particle labels: all five occupied sites are plotted identically.
for t,x in enumerate(trace): ax.scatter(x,[t]*5,s=2,c='#173f5f',edgecolors='none')
for b in data['boundaries']:
    ax.axhline(b['t'],color='#8b8b8b',linewidth=.7,linestyle=':')
    ax.text(190,b['t'],f"{b['q']}  t={b['t']}",va='center',fontsize=9)
ax.set_xlim(-196,265);ax.set_ylim(488,-16);ax.set_xticks([-180,-90,0,90,183]);ax.set_xlabel('Occupied lattice coordinate');ax.set_ylabel('CA tick');ax.set_title('A complete accepting trace with five occupied sites',loc='left',fontsize=11,pad=9)
ax.spines[['top','right']].set_visible(False)
bx=fig.add_subplot(gs[1]);bx.set_title('The zero test reads a fixed offset from the home marker',loc='left',fontsize=11,pad=9)
# A piecewise display separates the far sensor/endpoint from the close home geometry.
def fx(x): return 5*(x+180) if x < -100 else x+35
for row,(a,label) in enumerate([(0,'counter 0'),(1,'counter 1')]):
    y=1-row
    xs=[-180-a,0,11,14]
    bx.plot([-3,52],[y,y],color='#bbbbbb',lw=.7)
    bx.scatter([fx(x) for x in xs],[y]*4,s=28,color='#173f5f',zorder=4)
    bx.scatter([fx(-180)],[y],s=145,facecolors='none',edgecolors='#b05b27',linewidths=1.3,zorder=5)
    bx.text(-6,y,label,va='center',ha='right',fontsize=9)
    bx.text(57,y,'sensor 1 → zero branch' if a==0 else 'sensor 0 → decrement excursion',va='center',fontsize=9)
for x,label in [(-181,'−181'),(-180,'−180'),(0,'0'),(12.5,'11, 14')]:
    # avoid overlapping the two adjacent remote coordinate labels
    if x==-181: bx.text(fx(x),-.36,label,ha='center',fontsize=8)
    elif x==-180: bx.text(fx(x),-.65,label,ha='center',fontsize=8)
    else:bx.text(fx(x),-.36,label,ha='center',fontsize=8)
bx.text(20,.5,'//',ha='center',va='center',fontsize=14,color='#666666')
bx.text(0,1.36,'sensor at −Z',ha='center',fontsize=8,color='#8c421c')
bx.text(46,1.36,'home packet',ha='center',fontsize=8)
bx.set_xlim(-27,125);bx.set_ylim(-.82,1.6);bx.axis('off')
fig.savefig(P/'five-particle-trace.pdf',bbox_inches='tight')
fig.savefig(P/'five-particle-trace.png',dpi=160,bbox_inches='tight')
