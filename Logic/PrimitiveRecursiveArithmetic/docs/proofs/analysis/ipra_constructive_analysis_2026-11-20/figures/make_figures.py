"""Rebuild the two manuscript figures (Matplotlib, NumPy)."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
import numpy as np

OUT = Path(__file__).resolve().parent
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9,
                     "pdf.fonttype": 42, "axes.spines.top": False,
                     "axes.spines.right": False})
colors = ["#35637d", "#287b6a", "#ac582f"]

fig, ax = plt.subplots(figsize=(7.1, 2.25))
labels = [r"$\alpha(2)=0$", r"$\alpha(2)=1,\ \alpha(0)=0$",
          r"$\alpha(2)=1,\ \alpha(0)=1$"]
for row in range(3):
    y = 2-row
    ax.add_patch(Rectangle((0,y-.25),1,.5,facecolor="#f0f3f3",lw=0))
    for word in range(8):
        bit2, bit0 = word%2, word//4
        selected = 0 if bit2==0 else 1+bit0
        if selected == row:
            ax.add_patch(Rectangle((word/8,y-.25),1/8,.5,facecolor=colors[row],lw=0))
    ax.text(1.028,y,[r"$1/2$",r"$1/4$",r"$1/4$"][row],va="center")
ax.text(1.028,2.53,"Weight",ha="left",va="center",fontsize=8,color="#41545d")
ax.set_yticks([2,1,0], labels)
ax.set_xticks([0,1/4,1/2,3/4,1],["0","1/4","1/2","3/4","1"])
for n in range(9):
    ax.plot([n/8]*2,[-.28,2.27],color="white",lw=.45)
ax.set_xlim(0,1); ax.set_ylim(-.45,2.65)
ax.set_xlabel("Dyadic cells of width 1/8",labelpad=3)
ax.spines["left"].set_visible(False); ax.tick_params(axis="y",length=0,pad=6)
fig.subplots_adjust(left=.28,right=.91,bottom=.24,top=.94)
fig.savefig(OUT/"sparse-cylinders.pdf",bbox_inches="tight",pad_inches=.035)
plt.close(fig)

fig,ax=plt.subplots(figsize=(7.05,2.75))
f=lambda x:(x-.25)*(x-.5)*(x-.75)
x=np.linspace(.18,.82,501)
ax.axhline(0,color="#778a90",linewidth=.8)
ax.plot(x,f(x),color="#214c65",linewidth=1.8)
u=np.linspace(1/3,2/3,4)
ax.scatter(u,f(u),s=31,color=colors[1],zorder=3)
ax.scatter([.25,.5,.75],[0]*3,facecolor="white",s=34,linewidth=1.25,edgecolor="#214c65",zorder=4)
ax.annotate(r"$+5/864$",(1/3,f(1/3)),xytext=(.31,.0097),
            arrowprops={"arrowstyle":"-","lw":.65},ha="center",fontsize=8.5)
ax.annotate(r"$-5/864$",(2/3,f(2/3)),xytext=(.70,-.0103),
            arrowprops={"arrowstyle":"-","lw":.65},ha="center",fontsize=8.5)
ax.set_ylim(-.0135,.0135);ax.set_xlim(.18,.82)
ax.set_yticks([-.01,0,.01],["−0.01","0","0.01"])
ax.set_xticks([.25,1/3,.5,2/3,.75],["1/4","1/3","1/2","2/3","3/4"])
ax.set_xlabel("Position in the initial bracket");ax.set_ylabel("Polynomial value")
fig.subplots_adjust(left=.12,right=.97,top=.98,bottom=.22)
fig.savefig(OUT/"root-probes.pdf",bbox_inches="tight",pad_inches=.035)
