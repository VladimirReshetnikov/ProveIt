"""Reproduce illustrations with matplotlib's default color cycle."""
from pathlib import Path
import csv
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent.parent
out = ROOT/'figures'
out.mkdir(exist_ok=True)
constants = json.loads((ROOT/'data'/'constants.json').read_text())['constants']
rows = list(csv.DictReader((ROOT/'data'/'finite_moments.csv').open()))
plt.figure(figsize=(6.7,3.65))
plt.plot([int(x['n']) for x in rows], [float(x['centered_sqrt']) for x in rows],
         'o-', label='Exact counts, rounded moment')
plt.axhline(float(constants['c_star']), linestyle='--', label='Proved limiting constant')
plt.xscale('log', base=2)
plt.xlabel('Permutation size $n$')
plt.ylabel(r'$\mathbb{E}\sqrt{D_n}-\frac{3}{2\sqrt{\pi}}\log n$')
plt.legend(frameon=False, fontsize=9)
plt.tight_layout()
plt.savefig(out/'centered_moment.pdf')
plt.close()

x = np.linspace(0,1,401)
plt.figure(figsize=(6.7,3.65))
for lam in [-2,0,2]:
    phi = np.expm1(lam)/lam if lam else 1
    plt.plot(x,np.exp(lam*x)/phi, label=rf'$\lambda={lam}$')
plt.xlabel(r'Logarithmic scale $t=\log D_n/\log n$')
plt.ylabel('Limiting tilted density')
plt.legend(frameon=False)
plt.tight_layout()
plt.savefig(out/'tilted_densities.pdf')
plt.close()

hist = json.loads((ROOT/'data'/'exact_distributions.json').read_text())
plt.figure(figsize=(6.7,3.65))
for n in [16,32,64]:
    weights = np.sqrt(np.arange(n+1))*np.array(hist[str(n)],dtype=float)
    weights /= weights.sum()
    pos = np.log(np.arange(1,n+1))/np.log(n)
    plt.step(pos,np.cumsum(weights[1:]),where='post',label=rf'$n={n}$')
plt.plot(x,x,'--',label='Uniform limiting distribution')
plt.xlabel(r'$t=\log D_n/\log n$')
plt.ylabel('Square-root-biased distribution function')
plt.legend(frameon=False,fontsize=9)
plt.tight_layout()
plt.savefig(out/'biased_distribution.pdf')
plt.close()
print('Three figures written.')
