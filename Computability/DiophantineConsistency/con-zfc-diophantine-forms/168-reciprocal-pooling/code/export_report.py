#!/usr/bin/env python3
"""Render the fixed residual list and artifact identities as ordinary LaTeX."""
from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def render_term(c, mon, first=False):
    powers=Counter(mon)
    factors=''.join('x_{'+str(j)+'}'+('^{'+str(k)+'}' if k>1 else '') for j,k in sorted(powers.items()))
    magnitude=str(abs(c)) if not factors or abs(c)!=1 else ''
    sign='-' if c<0 else ('' if first else '+')
    return sign+magnitude+factors


def term_width(c,mon):
    powers=Counter(mon)
    return 1.0+(0.6*len(str(abs(c))) if abs(c)!=1 or not mon else 0)+sum(1.8+0.35*len(str(j))+(0.7 if k>1 else 0) for j,k in powers.items())


def render_rows(eq):
    parts=['% Generated from equations/quartic218/equation.json. Actual math is parsed by check_report.py.']
    for i,row in enumerate(eq['residuals']):
        chunks=[];line='';width=0
        for k,(c,m) in enumerate(row['terms']):
            term=render_term(c,m,k==0); tw=term_width(c,m)
            if line and width+tw>42:
                chunks.append(line);line='';width=0
            line+=term;width+=tw
        chunks.append(line or '0')
        parts.append('% RESIDUAL '+str(i))
        parts.append(r'\begin{equation*}\begin{aligned}')
        parts.append('Q_{'+str(i)+r'}={}& '+chunks[0]+(r'\\' if len(chunks)>1 else ''))
        for k,chunk in enumerate(chunks[1:],1):
            parts.append(r'& '+chunk+(r'\\' if k<len(chunks)-1 else ''))
        parts.append(r'\end{aligned}\end{equation*}')
    return '\n'.join(parts)+'\n'


def build():
    report=ROOT/'report'
    eq=json.loads((ROOT/'equations/quartic218/equation.json').read_text())
    (report/'residuals218.tex').write_text(render_rows(eq))
    (report/'metrics.tex').write_text('% Frozen dimensions; full metric records are in equations/.\n'+r'\newcommand{\PrincipalVariables}{218}'+'\n'+r'\newcommand{\CompanionVariables}{215}'+'\n')
    lines=[r'\begin{longtable}{@{}p{0.26\textwidth}p{0.69\textwidth}@{}}',r'\toprule Artifact & SHA-256 of the supplied file\\\midrule']
    paths=['equations/quartic218/equation.json','equations/quartic218/expanded_polynomial.json',
           'equations/decic215/equation.json','equations/decic215/expanded_polynomial.json']
    for path in paths:
        label=path.replace('equations/','').replace('expanded_polynomial.json','expanded polynomial').replace('equation.json','residuals')
        h=hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
        lines.append(label.replace('_',r'\_')+r' & {\scriptsize\ttfamily '+h[:32]+r'\newline '+h[32:]+r'}\\')
    lines.append(r'\bottomrule\end{longtable}')
    (report/'identities.tex').write_text('\n'.join(lines)+'\n')
    print(json.dumps({'residuals':len(eq['residuals']),'rendered':'report/residuals218.tex','identities':paths}))


if __name__=='__main__':
    build()
