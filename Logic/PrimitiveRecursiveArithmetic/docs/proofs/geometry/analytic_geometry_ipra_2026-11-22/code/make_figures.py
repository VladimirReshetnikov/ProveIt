"""Produce exact-formula illustrative plots; figures are not proof evidence."""
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10, 'axes.titlesize': 11})
fig, axes = plt.subplots(2, 3, figsize=(10.2, 6.4), constrained_layout=True)
navy, teal, rust = '#16324F', '#168A8A', '#B65136'
theta = np.linspace(0, 2*np.pi, 700)
titles = [r'$x^2+y^2=1$: circle', r'$x^2+y^2=0$: point', r'$x^2+y^2=-1$: empty', r'$y=x^2$: parabola', r'$x^2-y^2=1$: hyperbola', r'$x^2-y^2=0$: crossing lines']
for ax, title in zip(axes.flat, titles):
    ax.set_title(title, color=navy, pad=10)
    ax.set_xlim(-2.1,2.1); ax.set_ylim(-2.1,2.1); ax.set_aspect('equal')
    ax.axhline(0, color='#B4BEC7', lw=.7); ax.axvline(0, color='#B4BEC7', lw=.7)
    ax.set_xticks([-2,0,2]); ax.set_yticks([-2,0,2]); ax.tick_params(labelsize=8)
    for sp in ax.spines.values(): sp.set_color('#D3D9DE')
axes[0,0].plot(np.cos(theta),np.sin(theta),color=teal,lw=2.1)
axes[0,1].plot([0],[0],'o',color=teal,markersize=6)
axes[0,2].text(0,.65,'No real points',ha='center',color=rust,fontsize=11)
t=np.linspace(-1.44,1.44,500)
axes[1,0].plot(t,t*t,color=teal,lw=2.1)
t=np.linspace(-1.35,1.35,500)
for sign in [-1,1]: axes[1,1].plot(sign*np.cosh(t),np.sinh(t),color=teal,lw=2.1)
for sign in [-1,1]: axes[1,2].plot([-2.1,2.1],[-2.1*sign,2.1*sign],color=teal,lw=2.1)
fig.suptitle('A conic label needs degeneracy and real-point information',fontsize=14,color=navy)
folder=Path(__file__).resolve().parents[1]/'figures'; folder.mkdir(exist_ok=True)
fig.savefig(folder/'conic_loci.pdf')
fig.savefig(folder/'conic_loci.png',dpi=160)
plt.close(fig)
print('Created figures/conic_loci.pdf and .png')
