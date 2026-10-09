#!/usr/bin/env python3
"""Regenerate LaTeX tables from checked result JSON.

Interval endpoints are rounded outward with integer/rational arithmetic.
The asymptotic-comparison table is explicitly non-rigorous numerical evidence.
"""
from __future__ import annotations
from pathlib import Path
from fractions import Fraction
import json

ROOT=Path(__file__).resolve().parents[1]

def rounded_endpoint(value: str, upper: bool=False, digits:int=8) -> str:
    q=Fraction(value)*10**digits
    x=-((-q.numerator)//q.denominator) if upper else q.numerator//q.denominator
    sign='-' if x<0 else '';x=abs(x)
    return f'{sign}{x//10**digits}.{x%10**digits:0{digits}d}'

def main() -> None:
    exact=json.loads((ROOT/'data/exact_results.json').read_text())
    numerical=json.loads((ROOT/'data/numerical_results.json').read_text())
    if exact['status']!='PASS' or numerical['status']!='PASS':
        raise ValueError('only passing result records may be rendered')
    results=exact['results']
    if len(results)!=30:
        raise ValueError('unexpected certificate layout; inspect before rendering')
    rows=[r'\begin{center}',r'\begin{tabular}{cclc}',r'\toprule',
          r'$n$ & $a$ & Certified enclosure for $\mathcal V_{n,1}(a)$ & Sign\\',r'\midrule']
    for item in results[:14]:
        lo,hi=item['enclosure'];sign='+' if item['verified_sign']>0 else '-'
        if item['k']!=1:raise ValueError('unexpected base-case record')
        rows.append(fr"{item['n']} & ${item['a']}$ & $[{rounded_endpoint(lo)},\ {rounded_endpoint(hi,True)}]$ & ${sign}$\\")
    rows += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'article/base-sign-table.tex').write_text('\n'.join(rows)+'\n')

    rows=[r'\begin{center}',r'\begin{tabular}{rl}',r'\toprule',
          r'$k$ & Certified lower endpoint $\ell_k$\\',r'\midrule']
    for index in range(14,30,2):
        lo,hi=results[index:index+2]
        if not (lo['n']==hi['n']==1 and lo['k']==hi['k'] and
                Fraction(hi['a'])-Fraction(lo['a'])==Fraction(1,10**20) and
                lo['verified_sign']==1 and hi['verified_sign']==-1):
            raise ValueError('root interval records do not match')
        rows.append(fr"{lo['k']} & ${lo['a']}$\\")
    rows += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'article/root-interval-table.tex').write_text('\n'.join(rows)+'\n')

    rows=[r'\begin{center}',r'\begin{tabular}{rrr}',r'\toprule',
          r'$k$ & $\alpha_k-A_k$ (numerical) & $(k+1)^2(\alpha_k-A_k)$\\',r'\midrule']
    for a in numerical['roots']:
        if a['k'] not in [20,50,100,200,500]:continue
        mant,ex=f"{float(a['second_order_error']):.9e}".split('e')
        rows.append(fr"{a['k']} & ${mant}\times10^{{{int(ex)}}}$ & ${float(a['scaled_second_order_error']):.12f}$\\")
    rows += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'article/asymptotic-table.tex').write_text('\n'.join(rows)+'\n')
    print('Regenerated three LaTeX tables; certificate endpoints rounded outward.')

if __name__=='__main__':main()
