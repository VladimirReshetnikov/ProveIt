#!/usr/bin/env python3
"""Render the exact final residual JSON as a typeset polynomial appendix."""
from collections import Counter
from pathlib import Path
import hashlib,json

ROOT=Path(__file__).resolve().parent.parent
src=ROOT/'direct/equation/equation.json'
d=json.loads(src.read_text())
if len(d['variables'])!=252 or len(d['residuals'])!=182:
    raise ValueError('Unexpected final equation dimensions')

def texterm(c,mon,first):
    sign=('-' if c<0 else '') if first else (' - ' if c<0 else ' + ')
    a=abs(c); count=Counter(mon)
    coeff=str(a) if a!=1 or not mon else ''
    factors=''.join('z_{'+str(i)+'}'+('^{'+str(e)+'}' if e>1 else '') for i,e in sorted(count.items()))
    return sign+coeff+factors

lines=[r'\begingroup',r'\small',r'\setlength{\jot}{3pt}',r'\begin{align*}']
for i,row in enumerate(d['residuals']):
    terms=row['terms'];chunks=[];chunk='';weight=0
    for j,(c,mon) in enumerate(terms):
        term=texterm(c,mon,j==0)
        w=3+len(str(abs(c)))+5*len(set(mon))
        if chunk and weight+w>65:
            chunks.append(chunk);chunk='';weight=0
        chunk+=term;weight+=w
    if chunk:chunks.append(chunk)
    for j,ch in enumerate(chunks):
        pref='Q_{'+str(i)+'} &={}' if j==0 else r'&\quad{}'
        last_chunk = j == len(chunks)-1
        final_line = i == len(d['residuals'])-1 and last_chunk
        tail = '' if final_line else (r'\\[4pt]' if last_chunk else r'\\*')
        lines.append(pref+ch+tail)
lines += [r'\end{align*}',r'\endgroup','']
(ROOT/'report/residuals.tex').write_text('\n'.join(lines))
out={'equation_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'variables':252,'residuals':182,'appendix_sha256':hashlib.sha256((ROOT/'report/residuals.tex').read_bytes()).hexdigest()}
(ROOT/'verification/appendix_generation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
