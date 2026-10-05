#!/usr/bin/env python3
"""Prepare the independent 113-bit direct-product audits."""
import os
import mpmath as mp
from diagnostics import select_case
root=os.path.dirname(__file__)
for a,lam,phase,stem,J in [(8,4,0,'a8_l4_phase0',8),(12,5,.5,'a12_l5_phasehalf',10)]:
    s=select_case(a,lam,phase)
    with open(os.path.join(root,stem+'.txt'),'w') as f:
        f.write(f"{a} {s['K']} {s['n']} {J} {len(s['ks'])}\n")
        f.write(' '.join(str(x) for x in s['ks'])+'\n')
mp.mp.dps=60
for N in [96,128]:
    x,w=mp.gauss_quadrature(N,'legendre')
    with open(os.path.join(root,f'nodes{N}.txt'),'w') as f:
        f.write(str(N)+'\n')
        for a,b in zip(x,w):f.write(mp.nstr(11*a,55)+' '+mp.nstr(11*b,55)+'\n')
