"""Rebuild the mathematical branch and alphabet diagram (no network)."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle

root = Path(__file__).resolve().parents[1]
out = root / "figures"
out.mkdir(exist_ok=True)
plt.rcParams.update({"font.family":"DejaVu Sans", "font.size":10,
                    "axes.spines.top":False, "axes.spines.right":False,
                    "axes.labelcolor":"#25354a", "text.color":"#25354a",
                    "axes.edgecolor":"#718094", "pdf.fonttype":42})
fig, ax = plt.subplots(1,2,figsize=(10.0,3.65),layout="constrained")
blue, red = "#126b9c", "#c1584b"
t = np.linspace(0,1,400)
w = (1+1j*t)/(1+t*t)
a=ax[0]
a.axhline(0,color="#b8c1cc",lw=.8)
a.axvline(0,color="#b8c1cc",lw=.8)
a.plot([1,1.32],[0,0],color=red,lw=4,solid_capstyle="butt")
a.plot(w.real,w.imag,color=blue,lw=2.4)
a.scatter([1,.5],[0,.5],color=blue,s=32,zorder=4)
a.annotate("$1$",(1,0),xytext=(3,9),textcoords="offset points")
a.annotate("$(1+i)/2$",(.5,.5),xytext=(-12,13),textcoords="offset points")
a.annotate("$w(t)=(1+it)/(1+t^2)$",(.88,.32),xytext=(.11,.7),
           arrowprops={"arrowstyle":"-","color":"#718094"})
a.annotate("$t:0\\to1$",(.71,.455),xytext=(.83,.59),
           arrowprops={"arrowstyle":"->","color":blue})
a.text(1.07,.095,"cut",color=red,fontsize=9)
a.set(xlim=(-.07,1.34),ylim=(-.13,.83),xlabel="Real part",ylabel="Imaginary part")
a.set_aspect("equal")
a.set_title("A. The reciprocal complementary path",loc="left",pad=15,fontsize=11)

a=ax[1]
x=np.linspace(-1.4,2.1,600)
y=np.linspace(-1.4,1.4,500)
X,Y=np.meshgrid(x,y)
allowed=(X*X+Y*Y>=1)&((1-X)**2+Y*Y>=1)
a.contourf(X,Y,allowed.astype(float),levels=[-.5,.5,1.5],colors=["#ffffff","#e0edf4"])
for center in (0,1):
    a.add_patch(Circle((center,0),1,fill=False,color="#8a9aac",lw=1.1))
a.axhline(0,color="#b8c1cc",lw=.6)
a.axvline(0,color="#b8c1cc",lw=.6)
pts=[(-1,0,"$-1$",(-15,8)),(0,1,"$i$",(7,5)),(0,-1,"$-i$",(7,-15)),
     (1,-1,"$1-i$",(8,-6)),(0,0,"$0$",(-12,-15)),(1,0,"$1$",(7,6))]
for x0,y0,label,offset in pts:
    a.scatter([x0],[y0],s=27,color=blue,zorder=5)
    a.annotate(label,(x0,y0),xytext=offset,textcoords="offset points",fontsize=10)
a.set(xlim=(-1.4,2.1),ylim=(-1.4,1.4),xlabel="Real part",ylabel="Imaginary part")
a.set_aspect("equal")
a.set_title("B. Exact-certificate letter region",loc="left",pad=15,fontsize=11)
fig.savefig(out/"branch_and_alphabet.pdf",bbox_inches="tight")
fig.savefig(out/"branch_and_alphabet.png",dpi=200,bbox_inches="tight")
print("Wrote figures/branch_and_alphabet.{pdf,png}")
