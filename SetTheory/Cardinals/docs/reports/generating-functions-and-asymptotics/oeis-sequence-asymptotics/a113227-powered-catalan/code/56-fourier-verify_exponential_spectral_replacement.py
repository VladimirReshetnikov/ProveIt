"""Non-certified high-precision diagnostic of global spectral replacement.

Compares exact recurrence moments with an exact-Bessel integer lattice sum.
The finite numerical lattice tail is not an interval enclosure; the proof,
not this diagnostic, establishes every exponent d<log(2).
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps=180
indices=[80,160,320]
p=[1]
exact={0:1}
for n in range(1,max(indices)+1):
    suffix=0
    nxt=[0]*(n+1)
    for k in range(n,0,-1):
        if k<len(p):suffix+=p[k]
        nxt[k]=p[k-1]+k*suffix
    p=nxt
    if n in indices:exact[n]=sum(p)

K=8
max_r=max(mp.mpf(n)/mp.lambertw(mp.mpf(n)/mp.e) for n in indices)
upper=int(mp.ceil(6*max_r))
weights=[]
for k in range(K,upper+1):
    t=mp.mpf(k)
    b=mp.sqrt(t)*mp.bessely(t+1,2*mp.sqrt(t))-mp.bessely(t,2*mp.sqrt(t))
    weights.append(1/(mp.pi**2*t*b*b))
results=[]
for n in indices:
    lattice=mp.fsum(Q*mp.mpf(k)**n for k,Q in zip(range(K,upper+1),weights))
    rel=lattice/exact[n]-1
    item={'n':n,'relative_lattice_minus_exact':mp.nstr(rel,35),
          'observed_exponential_rate':mp.nstr(-mp.log(abs(rel))/n,25)}
    results.append(item)
    print(item,flush=True)
out={'precision_digits':mp.mp.dps,'K':K,'upper_integer_cutoff':upper,
     'note':'Numerical diagnostic; finite tail not interval certified; log(2) is the upper endpoint of proved permissible exponents, not claimed optimal',
     'results':results}
path=Path(__file__).with_name('exponential_spectral_replacement_diagnostics.json')
path.write_text(json.dumps(out,indent=2)+'\n')
