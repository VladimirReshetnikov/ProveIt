"""Draw the two P6--P9 paths after reflection of the target in L."""
from fractions import Fraction as Q
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from geometry import SCALE, point_box, gate_box

def middle(box):
    return np.array([(l+r)/(2*SCALE) for l,r in box])

p,q=map(lambda n:middle(point_box(n)),('P6','P9'))
q[0]=-q[0]
o=middle(gate_box('L',Q(1)))
s=p+(q-p)*(-p[0]/(q[0]-p[0]))
curve=np.array([middle(gate_box('B', Q(k,10000))) for k in range(9600,10001,5)])
fig,axes=plt.subplots(1,2,figsize=(7.7,1.70),width_ratios=(1.9,1),layout='constrained')
for ax in axes:
    ax.plot([0,0],[1.55,o[1]],color='#607878',lw=1.25)
    ax.plot(curve[:,0],curve[:,1],color='#607878',lw=1.25)
    ax.plot([q[0],o[0],p[0]],[q[1],o[1],p[1]],color='#ad5536',ls=(0,(4,3)),lw=1.7)
    ax.plot([q[0],p[0]],[q[1],p[1]],color='#13766b',lw=1.6)
    ax.axis('off')
ax=axes[0]
ax.set(xlim=(-.6,.25),ylim=(1.619,1.807))
ax.scatter(*p,s=15,color='#193d47');ax.scatter(*q,s=15,color='#193d47')
ax.annotate('$P_6$',p,(5,1),textcoords='offset points',fontsize=9)
ax.annotate("reflected $P_9$",q,(0,-12),textcoords='offset points',fontsize=8)
ax.annotate('B',curve[9],(5,-3),textcoords='offset points',fontsize=8)
ax.text(.008,1.643,'L',fontsize=8)
ax.add_patch(plt.Rectangle((-.010,s[1]-.0012),.020,.0044,fill=False,lw=.9,ls=':',ec='#344b53'))
ax=axes[1]
ax.set(xlim=(-.009,.011),ylim=(s[1]-.0010,o[1]+.00145))
ax.scatter(*s,s=16,color='#13766b',zorder=4);ax.scatter(*o,s=16,color='#ad5536',zorder=4)
ax.annotate('B endpoint',o,(-48,10),textcoords='offset points',fontsize=8,color='#823e2d')
ax.annotate('L contact',s,(5,-14),textcoords='offset points',fontsize=8,color='#0a645a')
fig.savefig(Path(__file__).resolve().parents[1]/'figures'/'close_pair.pdf',bbox_inches='tight',pad_inches=.02)
