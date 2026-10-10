#!/usr/bin/env python3
"""Reproduce the moment-transition and exact parameter-domain figures."""
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
FIG=ROOT/"figures"
NAVY,TEAL,RUST="#183B50","#258F8B","#B86743"
plt.rcParams.update({"font.family":"STIXGeneral","mathtext.fontset":"stix","font.size":10,"axes.spines.top":False,"axes.spines.right":False,"axes.edgecolor":"#68747B","axes.linewidth":0.65,"text.color":NAVY,"axes.labelcolor":NAVY,"legend.fontsize":9,"pdf.fonttype":42,"savefig.facecolor":"white"})


def save(fig,name):
    for ext in ("pdf","png"):fig.savefig(FIG/f"{name}.{ext}",dpi=220,bbox_inches="tight")
    plt.close(fig)


def gamma_figure():
    rows=json.loads((ROOT/"data/gamma_diagnostics.json").read_text())["rows"]
    fig,axes=plt.subplots(1,2,figsize=(7.25,3.15))
    for c,color,marker in [(-1,RUST,"s"),(0,NAVY,"o"),(1,TEAL,"^")]:
        data=[v for v in rows if v["c"]==c]
        m=np.array([v["m"] for v in data]);ratio=np.array([float(v["ratio_t"]) for v in data]);lim=float(data[0]["limit"])
        axes[0].plot(m,ratio,color=color,marker=marker,markersize=4,linewidth=1.4,label=fr"$c={c}$")
        axes[0].axhline(lim,color=color,linestyle=(0,(3,3)),linewidth=.8,alpha=.8)
        axes[1].plot(m,[float(v["scaled_relative_error"]) for v in data],color=color,marker=marker,markersize=4,linewidth=1.4,label=fr"$c={c}$")
    axes[0].set(xscale="log",yscale="log",xlabel="Reflected exponent $m$",ylabel="Normalized moment",title="(a)  Critical limiting factors")
    axes[0].set_yticks([1,2,5,10]);axes[0].set_yticklabels(["1","2","5","10"])
    axes[0].legend(frameon=False,loc="center right")
    axes[1].set(xscale="log",yscale="symlog",xlabel="Reflected exponent $m$",ylabel=r"$(R/e^{Cq}-1-P_1/m)m^2/L^2$",title="(b)  Remainder after first correction")
    axes[1].set_yscale("symlog",linthresh=.02,linscale=.45)
    axes[1].axhline(0,color="#CED6D9",linewidth=.7)
    axes[1].legend(frameon=False,loc="center left")
    for ax in axes:
        ax.set_xticks([20,100,500,2000]);ax.set_xticklabels(["20","100","500","2000"])
        ax.tick_params(labelsize=8.5)
    fig.tight_layout(w_pad=1.7)
    save(fig,"gamma_transition")


def domain_figure():
    fig,ax=plt.subplots(figsize=(5.8,3.55))
    a=np.linspace(0,2,401)
    ax.fill_between(a,np.maximum(0,1-a),2.4,color="#E2F0EE")
    ax.fill_between(a,0,np.maximum(0,1-a),color="#F8ECE5")
    ax.plot([0,1],[1,0],color=TEAL,linewidth=2.2)
    ax.plot([0,0],[1,2.4],color=TEAL,linewidth=3)
    ax.scatter([0,1],[1,0],facecolor="white",edgecolor=TEAL,s=45,zorder=6,linewidths=1.6)
    ax.text(1.18,1.6,"Integrable density\nOne strict sign change",ha="center",va="center",color=NAVY,fontsize=11)
    ax.text(.26,.24,"No finite\nsigned measure",ha="center",va="center",color=RUST,fontsize=10)
    ax.annotate("Positive atom at 1",xy=(.48,.52),xytext=(1.15,.77),ha="center",color=TEAL,arrowprops={"arrowstyle":"-","color":TEAL,"lw":.8})
    ax.annotate("Atomic edge",xy=(.01,1.83),xytext=(.34,2.15),ha="center",color=TEAL,arrowprops={"arrowstyle":"-","color":TEAL,"lw":.8})
    ax.annotate("Excluded corner",xy=(0,1),xytext=(.38,1.19),color=RUST,arrowprops={"arrowstyle":"-","color":RUST,"lw":.8},fontsize=9)
    ax.set(xlim=(-.04,2),ylim=(0,2.4),xlabel="Outer order $a$",ylabel="Inner order $b$")
    ax.set_xticks([0,.5,1,1.5,2]);ax.set_yticks([.5,1,1.5,2])
    ax.spines["left"].set_position(("data",0));ax.spines["bottom"].set_position(("data",0))
    fig.tight_layout()
    save(fig,"signed_measure_domain")


if __name__=="__main__":
    FIG.mkdir(parents=True,exist_ok=True)
    gamma_figure();domain_figure()
    print("Created two vector figures and PNG previews.")
