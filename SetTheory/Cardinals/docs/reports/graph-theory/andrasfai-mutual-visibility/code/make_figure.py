#!/usr/bin/env python3
"""Regenerate the article's exact cardinality-distribution illustration."""
from pathlib import Path
import math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from visibility import polynomial

n = 20
length = 3*n-1
coefficients = polynomial(n)
total = sum(coefficients)
mu = 0.370526040195751563090487009118
variance_density = 0.128918101249168837027097668809
mean = mu*length
variance = variance_density*length
positions = list(range(len(coefficients)))
probabilities = [c/total for c in coefficients]
xs = [8+i*0.05 for i in range(561)]
normal = [math.exp(-(x-mean)**2/(2*variance))/math.sqrt(2*math.pi*variance) for x in xs]
fig, ax = plt.subplots(figsize=(7.2,3.8))
ax.bar(positions, probabilities, width=0.8, label='Exact probability')
ax.plot(xs, normal, linewidth=1.8, label='Limiting normal density')
ax.set(xlabel='Cardinality k', ylabel='Probability / density', xlim=(8,36), ylim=(0,0.16))
ax.legend(frameon=False)
ax.spines['top'].set_visible(False)
ax.spines['right'].set_visible(False)
fig.tight_layout()
folder=Path(__file__).resolve().parent.parent/'figures'
folder.mkdir(exist_ok=True)
fig.savefig(folder/'cardinality_distribution.pdf', bbox_inches='tight')
plt.close(fig)
