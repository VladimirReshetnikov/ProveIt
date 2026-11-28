#!/usr/bin/env python3
"""Reproducible geometric figure; it is illustrative, not a numerical proof."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root = Path(__file__).resolve().parents[1]
out = root / 'figures'
out.mkdir(exist_ok=True)
plt.rcParams.update({'font.size': 11, 'axes.spines.top': False,
                     'axes.spines.right': False, 'pdf.fonttype': 42})
omega = np.exp(2j*np.pi/3)
v = 3*np.array([1,omega,omega**2,1])
t = np.linspace(0,2*np.pi,1000)
curve = 2*np.exp(1j*t)+np.exp(-2j*t)
fig, ax = plt.subplots(figsize=(6.8,5.2))
ax.fill(v.real,v.imag,color='#e1edf4',label='Triangle containing every SU(3) trace')
ax.plot(3*np.cos(t),3*np.sin(t),'--',color='#8d969e',lw=1,label='Generic unitary trace bound')
ax.plot(curve.real,curve.imag,color='#12516c',lw=1.8,label=r'Traces of diag$(e^{it},e^{it},e^{-2it})$')
ax.plot(v.real,v.imag,color='#12516c',lw=1.2)
ax.plot([v[1].real,v[2].real],[v[1].imag,v[2].imag],color='#bb5737',lw=3)
ax.scatter(v[:3].real,v[:3].imag,s=36,color='#bb5737',zorder=5)
ax.text(3.10,0,r'$3$',va='center')
ax.text(-1.44,2.76,r'$3\omega$')
ax.text(-1.44,-2.98,r'$3\omega^2$')
ax.text(-2.89,0,r'$3\sqrt{3}$',ha='center',va='center',color='#9b4024')
ax.annotate('',xy=(-2.5,2.598),xytext=(-2.5,-2.598),
            arrowprops={'arrowstyle':'<->','color':'#bb5737','lw':1.1})
ax.axhline(0,color='#c7cdd2',lw=.6,zorder=-1)
ax.axvline(0,color='#c7cdd2',lw=.6,zorder=-1)
ax.set_aspect('equal')
ax.set(xlim=(-3.35,3.55),ylim=(-3.3,3.3),xlabel='Real part of the trace',ylabel='Imaginary part of the trace')
ax.legend(loc='upper center',bbox_to_anchor=(.5,-.15),frameon=False,fontsize=9)
fig.tight_layout()
fig.savefig(out/'trace_triangle.pdf',bbox_inches='tight')
fig.savefig(out/'trace_triangle.png',dpi=180,bbox_inches='tight')
