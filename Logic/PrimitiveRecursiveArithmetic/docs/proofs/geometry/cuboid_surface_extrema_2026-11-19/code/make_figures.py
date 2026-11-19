#!/usr/bin/env python3
"""Reproduce the report's vector scientific figures (numpy + matplotlib)."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parents[1] / "figures"
OUT.mkdir(exist_ok=True)
plt.rcParams.update({"font.family":"DejaVu Sans", "font.size":10,
                     "axes.spines.top":False, "axes.spines.right":False,
                     "pdf.fonttype":42})


def maps():
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 4.25), layout="constrained")
    a=b=1.; c=2.
    for ax, size, mode in zip(axes, [1., .5], ["vertex", "antipodal"]):
        t=np.linspace(0,size,401)
        x,y=np.meshgrid(t,t)
        if mode=="vertex":
            q=np.minimum.reduce([(x+c)**2+y*y, x*x+(y+c)**2,
                 (a+c-x)**2+(a+y)**2, (b+x)**2+(b+c-y)**2])
            wx=wy=.75
            ax.set_title("Fixed vertex: target on z = 2",loc="left",weight="bold",pad=12)
            label=r"$Y=(3/4,3/4,2)$"
            ax.plot(1,1,"o",color="#334155",ms=5,clip_on=False)
            ax.annotate("opposite vertex",(1,1),xytext=(.48,.94),color="#334155",
                        arrowprops={"arrowstyle":"-","color":"#334155"})
        else:
            q=np.minimum.reduce([(a+c)**2+(b-2*y)**2,
                 (b+c)**2+(a-2*x)**2,(c+x+y)**2+(a+b-x-y)**2,
                 (a+b)**2+(c+2*y)**2,(a+b)**2+(c+2*x)**2])
            wx=wy=(np.sqrt(3)-1)/2
            ax.set_title("Free endpoints: X = (x, y, 0)",loc="left",weight="bold",pad=12)
            label=r"$x=y=(\sqrt{3}-1)/2$"
            ax.text(.025,.475,"Y = (1 − x, 1 − y, 2)",va="top",fontsize=9,color="#f8fafc")
        im=ax.pcolormesh(x,y,np.sqrt(q),cmap="viridis",rasterized=True,shading="auto")
        ax.contour(x,y,np.sqrt(q),levels=10,colors="white",linewidths=.45,alpha=.5)
        ax.plot(wx,wy,"*",color="#ef4444",ms=13,mec="white",mew=.7)
        ax.annotate(label,(wx,wy),xytext=(.05*size,.18*size),
                    bbox={"boxstyle":"round,pad=.25","fc":"white","ec":"none","alpha":.94},
                    arrowprops={"arrowstyle":"->","color":"white"})
        ax.set(xlim=(0,size),ylim=(0,size),xlabel="x",ylabel="y",aspect="equal")
        cb=fig.colorbar(im,ax=ax,fraction=.046,pad=.04)
        cb.set_label("Shortest surface distance")
    fig.savefig(OUT/"distance_maps.pdf")
    fig.savefig(OUT/"distance_maps.png",dpi=180)
    plt.close(fig)


def aspect():
    c=np.linspace(1,3.5,800)
    q0=c*c+4
    q1=(1+c*c)*(1+2*c+2*c*c)/(2*c*c)
    vertex=np.sqrt(np.maximum(q0,q1))
    diameter=np.where(c<=np.sqrt(2),np.sqrt(q0),
                      np.sqrt(3*c*c+2*c-2*c*np.sqrt(c*c-1)))
    fig,ax=plt.subplots(figsize=(8.2,4.2),layout="constrained")
    ax.plot(c,np.sqrt(q0),"--",color="#64748b",lw=1.7,label="Opposite vertices")
    ax.plot(c,vertex,color="#0284c7",lw=2.1,label="Maximum from a vertex")
    ax.plot(c,diameter,color="#b91c1c",lw=2.1,label="Both endpoints free")
    for t,col,text,yy in [(np.sqrt(2),"#b91c1c",r"$c=\sqrt{2}$",4.25),
                           ((3+np.sqrt(17))/4,"#0284c7",r"$c=(3+\sqrt{17})/4$",3.98)]:
        ax.axvline(t,color=col,alpha=.4,ls=":")
        ax.text(t+.035,yy,text,color=col,fontsize=10)
    ax.set(xlabel="Longest side c, for a = b = 1",ylabel="Shortest surface distance",
           xlim=(1,3.5),ylim=(2.15,4.7))
    ax.grid(alpha=.18)
    ax.legend(loc="lower right",frameon=False)
    ax.set_title("The two transitions occur at different aspect ratios",loc="left",weight="bold",pad=12)
    fig.savefig(OUT/"square_family.pdf")
    fig.savefig(OUT/"square_family.png",dpi=180)
    plt.close(fig)


if __name__=="__main__":
    maps()
    aspect()
