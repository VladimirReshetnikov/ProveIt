#!/usr/bin/env python3
"""Finite independent controls for the standard-integer carrier criterion."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-fixed-compact-carrier-gap'
pins={packet/'check.py':'4c1c34ad1ee38ea9c11ca0c96bb75da65da418e65a646d02a4b6966c0a912fa2',
      packet/'result.json':'7ac676546d7041d9daf80127bfc06082c31f82f5d63b7ad61454dcc2dd4290b3'}
for p,h in pins.items():
    if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('author artifact mismatch '+str(p))

# Directly test the modular core for all d in [0,mu), including nonzero d,
# for all possible gcd values e. This is independent of the q/X loops.
count=0
for e in (1,3,9):
    for mu in range(1,128):
        U=e*mu
        for d in range(mu):
            for multiple in range(1,2*e+2):
                h=mu*multiple
                if ((h+d)%U==0) != (d==0 and h%U==0):raise RuntimeError('criterion control failed')
                count+=1

# Independently recover the modular core of the reviewed full-zero negative
# control by modular Pell powering, without expanding its huge witnesses.
def power(x,y,d,n,mod):
    a,b=1,0
    for bit in bin(n)[2:]:
        a,b=(a*a+d*b*b)%mod,(2*a*b)%mod
        if bit=='1':a,b=(a*x+d*b*y)%mod,(a*y+b*x)%mod
    return a,b
m,n=19259,11720; U,H=729,759
g,c=power(191,1,36480,m,H)
delta=(g-6-189*c)%H
if delta%253:raise RuntimeError('carrier integrality check')
hmod=(243*(delta//253))%U
_,kmod=power(8749,2,4374*4375,n,U)
d=2*n-m-1
if (delta,hmod,kmod,d,d%243,(hmod+kmod-m-1)%U)!=(506,486,112,4180,49,292):
    raise RuntimeError('negative-control residue mismatch')
author=json.loads((packet/'result.json').read_text())
if author['counterexample']['gap']!=d or author['counterexample']['old_carrier_mod_U']!=292:
    raise RuntimeError('author result mismatch')
print(json.dumps({'status':'PASS','modular_controls':count,'counterexample_gap':d,
 'counterexample_old_carrier_mod_729':292,'scope':'standard-integer criterion, independent modular controls; no Lean or model-level proof'},sort_keys=True))
