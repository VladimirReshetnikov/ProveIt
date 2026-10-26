#!/usr/bin/env python3
"""Print all final coefficients in readable text and LaTeX."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
def term(c,mon,tex=False,first=False):
    sign='-' if c<0 else ('' if first else '+')
    a=abs(c);factors=[]
    for i in sorted(set(mon)):
        count=mon.count(i)
        name=('x_{'+str(i)+'}') if tex else 'x'+str(i)
        if count>1:name+=('^{'+str(count)+'}') if tex else '**'+str(count)
        factors.append(name)
    if tex:return sign+('' if a==1 and mon else str(a))+''.join(factors)
    if a!=1 or not mon:factors.insert(0,str(a))
    return sign+'*'.join(factors)
def export(folder):
    e=json.loads((folder/'equation.json').read_text())
    plain=[];latex=['% Complete literal residuals; generated from equation.json.','\\allowdisplaybreaks[4]','\\begin{align*}']
    for j,row in enumerate(e['residuals']):
        ts=row['terms']
        plain.append('R['+str(j)+'] = '+''.join(term(c,m,first=k==0) for k,(c,m) in enumerate(ts)))
        parts=[term(c,m,tex=True,first=k==0) for k,(c,m) in enumerate(ts)]
        chunks=[];current=''
        for part in parts:
            if current and len(current)+len(part)>110:chunks.append(current);current=''
            current+=part
        if current:chunks.append(current)
        latex.append('% RBEGIN '+str(j))
        for k,chunk in enumerate(chunks):
            prefix=('R_{'+str(j)+'}={}&') if k==0 else '&'
            latex.append(prefix+chunk+('\\\\[3pt]' if k==len(chunks)-1 else '\\\\*'))
        latex.append('% REND '+str(j))
    latex.append('\\end{align*}')
    (folder/'residuals.txt').write_text('\n'.join(plain)+'\n')
    (folder/'residuals.tex').write_text('\n'.join(latex)+'\n')
    (folder/'variables.tsv').write_text('index\tname\n'+'\n'.join(str(i)+'\t'+v['name'] for i,v in enumerate(e['variables']))+'\n')
if __name__=='__main__':export(ROOT/'equations/principal208')
