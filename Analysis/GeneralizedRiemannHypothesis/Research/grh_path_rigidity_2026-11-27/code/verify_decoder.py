#!/usr/bin/env python3
"""Check finite Poisson formulas and generate an explicitly illustrative plot."""
from pathlib import Path
import json
import numpy as np
from prime_decoder import (
    cayley_angle, ordinate_from_jump, exact_finite_moments,
    simulate_band, decode_observed_jumps, band_weights,
)

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / "data/zeta_first_150.json").read_text())
positive = np.array([float(x["gamma"]) for x in data["zeros"]])
signed = np.r_[-positive, positive]
assert np.max(np.abs(ordinate_from_jump(cayley_angle(signed)) - np.abs(signed))) < 1e-10
duration, height, primes, n = 1.0, 128.0, [2, 3, 5], 50000
mean, cov, count = exact_finite_moments(signed, duration, height, primes)
draws = simulate_band(signed, duration, height, primes, n, seed=20261127)
z = (draws.mean(axis=0) - mean) / np.sqrt(np.diag(cov) / n)
assert np.max(np.abs(z)) < 6, ("Monte Carlo mean mismatch", z)
assert np.max(np.abs(np.diag(np.cov(draws, rowvar=False)) / np.diag(cov) - 1)) < .04

# A deterministic synthetic path checks the factor 1/2 in the measure:
# listing +gamma and -gamma creates total absolute-jump rate 2.
g = 20.0
m, c, k = exact_finite_moments([-g, g], 3.0, 15.0, [2])
a = -np.pi * np.sqrt(2) / (15 * np.log(2)) * np.cos(g * np.log(2))
assert k == 2 and abs(m[0] - 2*a) < 1e-12
assert abs(c[0, 0] - 2*a*a/3) < 1e-12
obs = decode_observed_jumps([cayley_angle(g), -cayley_angle(g)], 3., 15., [2])
assert abs(obs[0] - 2*a/3) < 1e-12

rows=[]
for T in [32.,64.,128.]:
    mu, v, k = exact_finite_moments(signed, duration, T, primes)
    rows.append({"T":T,"signed_zeros_in_band":k,"mean":mu.tolist(),"covariance":v.tolist()})
result = {
    "status":"PASS",
    "scope":"Finite-dimensional implementation checks, not verification of an infinite theorem or zero certification.",
    "tests":["Cayley inversion", "symmetrization factor and Poisson moment identities", "jump-list decoder consistency", "Monte Carlo mean and variance"],
    "seed":20261127,"replicates":n,"mean_standard_errors":z.tolist(),
    "finite_zeta_band_results":rows,
}
(ROOT / "checks/decoder_checks.json").write_text(json.dumps(result,indent=2)+"\n")

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.stats import norm
plt.rcParams.update({"font.family":"DejaVu Sans","font.size":10,"axes.spines.top":False,"axes.spines.right":False})
fig, ax = plt.subplots(1,2,figsize=(9.4,3.55),constrained_layout=True)
standardized=(draws-mean)/np.sqrt(np.diag(cov))
xx=np.linspace(-4,4,401)
ax[0].hist(standardized[:,0], bins=65, range=(-4,4), density=True, color="#38658a",alpha=.65,label="Poisson jump experiment")
ax[0].plot(xx,norm.pdf(xx),color="#b26039",lw=1.8,label="Standard normal density")
ax[0].set(xlabel="Prime 2 estimate, centered and scaled",ylabel="Density",title="Finite band: 128 < |gamma| <= 256")
ax[0].legend(frameon=False,fontsize=8)
ax[1].scatter(standardized[:3000,0],standardized[:3000,1],s=3,alpha=.16,color="#38658a",rasterized=True)
corr=cov[0,1]/np.sqrt(cov[0,0]*cov[1,1])
ax[1].set(xlabel="Standardized prime 2 estimate",ylabel="Standardized prime 3 estimate",title=f"Finite-model correlation = {corr:.4f}",xlim=(-4,4),ylim=(-4,4))
ax[1].axhline(0,color="#999999",lw=.4);ax[1].axvline(0,color="#999999",lw=.4)
fig.savefig(ROOT / "papers/decoder_illustration.pdf")
fig.savefig(ROOT / "papers/decoder_illustration.png",dpi=170)
plt.close(fig)
print(json.dumps(result,indent=2))
