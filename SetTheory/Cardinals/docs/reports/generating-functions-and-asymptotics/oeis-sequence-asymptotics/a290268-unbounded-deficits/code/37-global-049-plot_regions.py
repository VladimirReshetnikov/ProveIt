from pathlib import Path
import os, tempfile
_cache=tempfile.TemporaryDirectory(prefix="a290268-plot-")
os.environ["MPLCONFIGDIR"]=_cache.name
os.environ["XDG_CACHE_HOME"]=_cache.name
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon,Patch

out=Path(__file__).parent
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'mathtext.fontset':'dejavusans'})
fig,ax=plt.subplots(figsize=(7.2,4.7),layout='constrained')
full=[(0,0),(.5,0),(0,.5)]
wide=[(0,0),(10/23,0),(0,.5)]
positive=[(.5,0),(420/931,0),(20/131,91/262)]
ax.add_patch(Polygon(full,closed=True,facecolor='#f7dfb3',edgecolor='#343e47',linewidth=1.3))
ax.add_patch(Polygon(wide,closed=True,facecolor='#9bc3df',edgecolor='#356887',linewidth=1.1))
ax.add_patch(Polygon(positive,closed=True,facecolor='#95c7ac',edgecolor='#3c7050',linewidth=1.1))
ax.text(.105,.16,'Density one\n$10q>3d$',ha='center',va='center',color='#173d56',fontsize=11)
ax.annotate('Eventually positive\n$40k+420q\\leq91d$',xy=(.42,.04),xytext=(.38,.21),ha='center',fontsize=10,arrowprops={'arrowstyle':'->','color':'#355d44'},color='#284d35')
ax.annotate('Remaining region',xy=(.24,.235),xytext=(.385,.355),ha='center',fontsize=10,arrowprops={'arrowstyle':'->','color':'#86622a'},color='#755522')
ax.set(xlim=(-.005,.525),ylim=(-.005,.525),xlabel='$d/(N-1)$',ylabel='$k/(N-1)$',title='Certified regions among the outside-bulk tail candidates')
ax.set_aspect('equal',adjustable='box')
ax.spines[['top','right']].set_visible(False)
ax.grid(False)
fig.savefig(out/'regions.pdf',bbox_inches='tight')
fig.savefig(out/'regions.png',dpi=190,bbox_inches='tight')
