"""Generate the article's scientific figures from reproducible numerical data."""
from pathlib import Path
import json
import sys
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from verify_herglotz import normalized_jet,remainder,asymptotic

plt.rcParams.update({
    "font.family":"DejaVu Sans","font.size":10,
    "axes.spines.top":False,"axes.spines.right":False,
    "axes.grid":True,"grid.alpha":.2,"axes.titleweight":"semibold",
    "pdf.fonttype":42,"savefig.bbox":"tight"
})
navy="#173B63"; teal="#13877C"; rust="#C06A35"
moment=json.loads((ROOT/"data/moment_checks.json").read_text())
rows=moment["moment_remainders"]
n=np.array([r["n"] for r in rows])
obs=np.array([float(r["error_over_first_omitted"]) for r in rows])
first=np.array([float(r["first_correction"]) for r in rows])
second=np.array([float(r["second_correction"]) for r in rows])
fig,axes=plt.subplots(1,2,figsize=(10.7,3.55),constrained_layout=True)
axes[0].plot(n,obs,"o",color=navy,label="Direct integral / omitted term",zorder=4)
axes[0].plot(n,first,"--",color=rust,label="Through 1/N")
axes[0].plot(n,second,"-",color=teal,label="Through 1/N²")
axes[0].axhline(.5,color="#888888",linewidth=.8)
axes[0].set(xlabel="Moment order n",ylabel="Signed remainder ratio",
            title="Half the first omitted term")
axes[0].legend(fontsize=8,loc="lower left")
axes[1].semilogy(n,np.abs(obs-first),"o--",color=rust,label="After first correction")
axes[1].semilogy(n,np.abs(obs-second),"s-",color=teal,label="After second correction")
axes[1].set(xlabel="Moment order n",ylabel="Absolute ratio discrepancy",
            title="Two computed corrections")
axes[1].legend(fontsize=8)
for ext in ["pdf","png"]:
    fig.savefig(ROOT/f"figures/moment_remainders.{ext}",dpi=190)
plt.close(fig)

sample=[]
for r in range(20,301,5):
    precision=int(r*np.log10(r))+100
    with mp.workdps(precision):
        e=remainder(r,mp.mpf(1),normalized_jet(r,1,1))
        amp,phase,kappa=asymptotic(r,mp.mpf(1))
        sample.append({"r":r,"working_digits":precision,
            "E":mp.nstr(e,45),"amplitude":mp.nstr(amp,45),
            "normalized":mp.nstr(e/amp,40)})
        if r in [20,300]:
            with mp.workdps(precision+40):
                ee=remainder(r,mp.mpf(1),normalized_jet(r,1,1))
                assert abs(e-ee)<mp.mpf("1e-80")
xgrid=np.linspace(20,300,1400)
phase=2*np.sqrt(np.pi*xgrid)-np.pi-np.pi/8
kappa=3/(16*np.sqrt(2*np.pi))+(2*np.pi)**1.5/12
leading=np.cos(phase)
corrected=leading+kappa/np.sqrt(xgrid)*np.cos(phase+np.pi/4)
fig,ax=plt.subplots(figsize=(10.7,3.6),constrained_layout=True)
ax.plot(xgrid,leading,"--",color=rust,linewidth=1.1,label="Leading cosine")
ax.plot(xgrid,corrected,color=teal,linewidth=1.4,label="With 1/√r correction")
ax.plot([a["r"] for a in sample],[float(a["normalized"]) for a in sample],
        "o",markersize=3.3,color=navy,label="Exact finite formula",zorder=4)
ax.axhline(0,color="#888888",linewidth=.7)
ax.set(xlabel="Derivative order r",ylabel="Eᵣ(1) / asymptotic amplitude",
       title="Herglotz derivatives: the exponentially small remainder oscillates")
ax.legend(fontsize=8,loc="upper right",ncol=3)
for ext in ["pdf","png"]:
    fig.savefig(ROOT/f"figures/herglotz_oscillation.{ext}",dpi=190)
plt.close(fig)
(ROOT/"data/figure_data.json").write_text(json.dumps({
    "herglotz_sample":sample,
    "status":"Floating-point figure data; proofs and exact certificates are separate."
},indent=2)+"\n")
print(f"Created two figures in PDF and PNG; {len(sample)} Herglotz samples.")

