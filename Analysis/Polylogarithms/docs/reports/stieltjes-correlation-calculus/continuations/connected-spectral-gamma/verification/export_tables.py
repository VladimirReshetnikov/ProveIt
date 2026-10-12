#!/usr/bin/env python3
"""Regenerate finite exact jump, Stieltjes primitive, and anomaly coefficients."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp
from sympy.functions.combinatorial.numbers import stirling
ROOT=Path(__file__).resolve().parents[1]

def main() -> None:
    data={'conventions':{
        'stirling':'unsigned Stirling numbers of the first kind',
        'jump':'P_m(L)=Im((L+i*pi)^m)/pi, for real L',
        'local_jet':'critical equal-line derivative of order m-1 equals coefficient*product(u_j)',
        'series':'F_m=u^m*gamma_0(a)+sum c_{m,r}*u^(m+r)*zeta(r+1,a)',
        'evidence':'Finite exact coefficient data; the article supplies the all-order proofs.'},'depths':[]}
    for m in range(1,13):
        rows=[]
        for j in range((m-1)//2+1):
            rows.append({'L_power':m-2*j-1,'pi_power':2*j,
                         'integer_coefficient':int((-1)**j*sp.binomial(m,2*j+1))})
        item={'m':m,'jump_terms':rows,
           'critical_jet_coefficient':str((-1)**m*sp.factorial(m-1)/m),
           'equal_mass_zeta_coefficients':[{'r':r,'coefficient':str((-1)**r*sp.factorial(m)*stirling(m+r,m,kind=1)/sp.factorial(m+r))} for r in range(1,9)]}
        if m>=2:
            co=[sp.S.One]+[sp.S.Zero]*6
            for j in range(1,m):
                for r in range(1,7):co[r]+=co[r-1]/sp.Integer(j)
            item['complete_homogeneous_harmonics']=[str(c) for c in co]
        data['depths'].append(item)
    dest=ROOT/'results'/'exact-coefficients.json'
    dest.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    print(f'Wrote {dest.name}: 12 depths, exact rational and integer coefficients.')
if __name__=='__main__':main()
