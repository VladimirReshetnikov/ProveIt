"""Reproduce the manuscript figures; no custom color palette is used."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from two_mode import kurtosis_frontier, chernoff
ROOT=Path(__file__).resolve().parents[1]

def save(name):
    plt.tight_layout()
    plt.savefig(ROOT/'figures'/f'{name}.pdf',bbox_inches='tight')
    plt.savefig(ROOT/'figures'/f'{name}.png',dpi=160,bbox_inches='tight')
    plt.close()

d=np.linspace(-1,1,501)
plt.figure(figsize=(6.5,3.8))
plt.plot(2*np.sqrt(2)*d,[kurtosis_frontier(x) for x in d],label='Sharp fixed-skewness frontier')
plt.axhline(15,linestyle='--',label='Variance-only bound')
plt.xlabel('Standardized skewness')
plt.ylabel('Maximum standardized fourth moment')
plt.ylim(8.5,15.6)
plt.legend(frameon=False)
save('kurtosis_frontier')

x=np.linspace(.01,25,400)
plt.figure(figsize=(6.5,3.8))
plt.semilogy(x,[chernoff(0,t)[0] for t in x],label='Zero-skewness two-mode bound')
plt.semilogy(x,[chernoff(1,t)[0] for t in x],linestyle='--',label='Variance-only rank-one MGF bound')
plt.xlabel('Threshold x (variance is 2)')
plt.ylabel('One-sided Chernoff upper bound')
plt.legend(frameon=False)
save('tail_bounds')

m=np.arange(2,401)
plt.figure(figsize=(6.5,3.8))
plt.plot(m,4/(1+1/np.sqrt(m)),label='Flat paired spectra')
plt.axhline(4,linestyle='--',label='Optimal universal constant 4')
plt.xlabel('Number m of positive modes (and m negative modes)')
plt.ylabel('Squared spectral distance / fourth-trace deficit')
plt.legend(frameon=False)
save('rigidity_constant')
print('Created three PDF figures and three PNG previews.')
