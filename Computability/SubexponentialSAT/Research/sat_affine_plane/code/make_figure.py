"""Optional exact geometric illustration; requires matplotlib."""
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

out=Path(__file__).resolve().parents[1]/'figures';out.mkdir(exist_ok=True)
colors=['#125C83','#CC7524','#758E3C']
fig,axes=plt.subplots(1,4,figsize=(11.6,3.1),layout='constrained')
for ax,(a,b),title in zip(axes,[(1,0),(0,1),(1,1),(1,2)],
                         ['$x$','$y$','$x+y$','$x+2y$']):
    for x in range(3):
        for y in range(3):
            group=(a*x+b*y)%3
            ax.scatter(x,y,s=650,color=colors[group],edgecolors='white',linewidths=1.7,zorder=3)
            ax.text(x,y,str(3*x+y),ha='center',va='center',color='white',fontsize=12,fontweight='bold',zorder=4)
    ax.set_title('Lines of '+title,fontsize=13,pad=12)
    ax.set(xlim=(-.5,2.5),ylim=(-.5,2.5),xticks=[0,1,2],yticks=[0,1,2],xlabel='$x$',ylabel='$y$',aspect='equal')
    ax.grid(color='#D9E0E5',linewidth=.7);ax.tick_params(length=0,labelsize=9)
    for spine in ax.spines.values():spine.set_visible(False)
fig.savefig(out/'affine_partitions.pdf',bbox_inches='tight')
fig.savefig(out/'affine_partitions.png',dpi=170,bbox_inches='tight')
