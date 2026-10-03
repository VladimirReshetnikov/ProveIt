"""Rebuild the exploratory report figure from exact counts and fitted constants.

Every n from 80 through 600 is plotted. The counts are exact, but rho and C
are fitted non-certified approximations. This plot is not a certificate.
"""
from pathlib import Path
from datetime import datetime, timezone
import json, csv, os, tempfile
os.environ.setdefault("MPLCONFIGDIR", str(Path(tempfile.gettempdir()) / "historic-tree-matplotlib"))
os.environ.setdefault("XDG_CACHE_HOME", str(Path(tempfile.gettempdir()) / "historic-tree-cache"))
import mpmath as mp
Path(os.environ["MPLCONFIGDIR"]).mkdir(parents=True, exist_ok=True)
Path(os.environ["XDG_CACHE_HOME"]).mkdir(parents=True, exist_ok=True)
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter

ROOT=Path(__file__).resolve().parent
mp.mp.dps=100
j=json.loads((ROOT/'data/producer/numerics_150dps.json').read_text())
rho=mp.mpf(j['rho']); C=mp.mpc(j['C_real'],j['C_imag'])
la=(13+1j*mp.sqrt(71))/2
K=2*C*rho**la/mp.gamma(3-la)
h={int(n):int(v) for n,v in (line.split() for line in (ROOT/'data/independent/exact_h_0_600.txt').read_text().splitlines())}
rows=[]
for n in range(80,601):
    R=mp.mpf(h[n])*rho**(n+3)/(30*mp.factorial(n+2))
    q1=2*mp.re(K*mp.gamma(n+3-la)/mp.gamma(n+3))
    scale=mp.mpf(n)**mp.mpf('6.5')
    rows.append((n,float(scale*(R-1)),float(2*mp.re(K*mp.exp(-1j*mp.im(la)*mp.log(n)))),float(mp.mpf(n)**13*(R-1-q1))))
(ROOT/'figures').mkdir(exist_ok=True)
with (ROOT/'figures/oscillation.csv').open('w',newline='') as f:
    w=csv.writer(f);w.writerow(['n','n^6.5*(R_n-1)','leading_cosine','n^13*(R_n-Q1(n))']);w.writerows(rows)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
fig,axs=plt.subplots(2,1,figsize=(6.3,4.5),sharex=True,gridspec_kw={'hspace':0.20})
ns=[r[0] for r in rows]
axs[0].plot(ns,[r[1]/1e4 for r in rows],color='#15384f',lw=1.7,label='Normalized exact counts with fitted radius')
axs[0].plot(ns,[r[2]/1e4 for r in rows],color='#a16a32',lw=1.3,ls='--',label='Leading cosine')
axs[0].set_ylabel(r'$n^{13/2}(R_n-1)\,/\,10^4$')
axs[1].plot(ns,[r[3]/1e12 for r in rows],color='#15384f',lw=1.5)
axs[1].set_ylabel(r'$n^{13}(R_n-Q_1(n))\,/\,10^{12}$')
axs[1].set_xlabel(r'$n$ (logarithmic scale)')
for ax in axs:
    ax.axhline(0,color='#aaaaaa',lw=.6,zorder=0)
    ax.grid(axis='y',color='#e0e0e0',lw=.5)
    ax.set_xscale('log')
    ax.set_xlim(78,620)
axs[1].set_xticks([80,100,150,200,300,400,600])
axs[1].xaxis.set_major_formatter(ScalarFormatter())
axs[1].minorticks_off()
fig.subplots_adjust(left=.13,right=.985,bottom=.11,top=.98)
fig.savefig(ROOT/'figures/oscillation.pdf',metadata={'Creator':'make_figure.py','CreationDate':datetime(2026,10,2,tzinfo=timezone.utc),'ModDate':datetime(2026,10,2,tzinfo=timezone.utc)})
print('Wrote figures/oscillation.pdf and .csv')
