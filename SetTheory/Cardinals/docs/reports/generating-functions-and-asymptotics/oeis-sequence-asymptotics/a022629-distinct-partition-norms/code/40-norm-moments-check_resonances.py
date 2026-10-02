#!/usr/bin/env python3
"""Fourier-resonance diagnostics at exact numerical saddles; not certificates."""
from pathlib import Path
import csv
import mpmath as mp
from verify import cutoff
mp.mp.dps=50
p=Path(__file__).resolve().parent/'data'
rows=[]
for old in csv.DictReader((p/'diagnostics.csv').open()):
    if old['n']!='5000':continue
    a=int(old['alpha']);t=mp.mpf(old['saddle_t'])
    s=-mp.lambertw(-t/a,-1);M=mp.exp(s);theta=2*mp.pi/M
    val=mp.mpf(0);ed=mp.exp(-t);decay=mp.mpf(1)
    for k in range(1,cutoff(a,t,40)+1):
        decay*=ed;w=k**a*decay;prob=w/(1+w);v=prob*(1-prob)
        val+=mp.log1p(-4*v*mp.sin(k*theta/2)**2)/2
    leading=-2*mp.pi**4*M/(3*a**3*(s-1)**3)
    row={'alpha':a,'n':5000,'M':mp.nstr(M,15),'s':mp.nstr(s,15),
         'first_resonance_modulus':mp.nstr(mp.exp(val),20),
         'log_modulus':mp.nstr(val,20),
         'leading_log_modulus_H_version':mp.nstr(leading,20)}
    rows.append(row);print(row)
with (p/'resonance_diagnostics.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
