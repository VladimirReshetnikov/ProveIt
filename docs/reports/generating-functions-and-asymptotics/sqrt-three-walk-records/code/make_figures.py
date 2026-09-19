#!/usr/bin/env python3
"""Optional figures; requires matplotlib. Verification does not require it."""
from pathlib import Path
from math import log10
import sys
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from record_walk import EvenTraceWalk

ROOT = Path(__file__).resolve().parent.parent
(ROOT/"figures").mkdir(exist_ok=True)
w = EvenTraceWalk(4)
N = 1500
xs = list(range(N+1))
values, low, high = [0], [0], [0]
s = lo = hi = 0
for n in range(1, N+1):
    s += w.step(n)
    lo, hi = min(lo,s), max(hi,s)
    values.append(s);low.append(lo);high.append(hi)
fig, ax = plt.subplots(figsize=(8.2, 3.8))
ax.plot(xs, values, linewidth=0.7, label=r"$S(N)$")
ax.step(xs, low, where="post", linewidth=1.6, label="Running minimum")
ax.step(xs, high, where="post", linewidth=1.6, label="Running maximum")
ax.set_xlabel(r"$N$")
ax.set_ylabel(r"$S(N)$")
ax.set_xlim(0,N)
ax.grid(alpha=0.25)
ax.legend(loc="lower left", ncol=3, frameon=False, fontsize=9)
fig.tight_layout()
fig.savefig(ROOT/"figures"/"walk_and_records.pdf")
fig.savefig(ROOT/"figures"/"walk_and_records.png",dpi=170)
plt.close(fig)

ks = list(range(1,61))
fig, ax = plt.subplots(figsize=(8.2,3.8))
ax.plot(ks, [log10(w.first_positive(k)) for k in ks], label=r"First occurrence of $+k$")
ax.plot(ks, [log10(w.first_negative(k)) for k in ks], label=r"First occurrence of $-k$")
ax.set_xlabel(r"Target magnitude $k$")
ax.set_ylabel(r"$\log_{10}$ of first-passage position")
ax.grid(alpha=0.25)
ax.legend(frameon=False)
fig.tight_layout()
fig.savefig(ROOT/"figures"/"first_passage_growth.pdf")
fig.savefig(ROOT/"figures"/"first_passage_growth.png",dpi=170)
plt.close(fig)
