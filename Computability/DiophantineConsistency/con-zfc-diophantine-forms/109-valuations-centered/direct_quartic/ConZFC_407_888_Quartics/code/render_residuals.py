#!/usr/bin/env python3
"""Generate the complete printed residual list directly from literal JSON."""
from pathlib import Path
from collections import Counter
import json

ROOT=Path(__file__).resolve().parents[1]

def term(coefficient,monomial):
    negative=coefficient<0;c=abs(coefficient)
    counts=Counter(monomial)
    factors=''.join('x_{'+str(i)+'}'+('^{'+str(e)+'}' if e>1 else '') for i,e in sorted(counts.items()))
    body=(str(c) if c!=1 or not factors else '')+factors
    # A conservative typographical width, in approximate text ems.
    width=0.58*len(str(c))*(c!=1 or not factors)+sum(2.5+0.4*(e>1) for e in counts.values())+1.1
    return ('-' if negative else '+'),body,width

def generate(name):
    equation=json.loads((ROOT/'equations'/name/'equation.json').read_text())
    symbol={'natural407':'R','integer888':'S','integer917':'T'}[name]
    lines=['% Generated from the checked literal residual data.','\\begingroup\\small',
           '\\allowdisplaybreaks[4]','\\setlength{\\jot}{2pt}','\\begin{align*}']
    for i,row in enumerate(equation['residuals']):
        chunks=[];current='';width=0
        for index,(c,m) in enumerate(row['terms']):
            sign,body,w=term(c,m)
            rendered=('-' if sign=='-' else '')+body if index==0 else sign+body
            if current and width+w>37:
                chunks.append(current);current=rendered;width=w
            else:current+=rendered;width+=w
        if current:chunks.append(current)
        for k,chunk in enumerate(chunks):
            prefix=symbol+'_{'+str(i)+'}={}&' if k==0 else '&{}'
            # Keep each residual together, including its continuation lines.
            suffix='\\\\[3pt]' if k==len(chunks)-1 else '\\\\*'
            lines.append(prefix+chunk+suffix)
    lines+=['\\end{align*}','\\endgroup','']
    dest=ROOT/'appendix';dest.mkdir(exist_ok=True)
    path=dest/(name+'_rows.tex');path.write_text('\n'.join(lines))
    return {'file':str(path.relative_to(ROOT)),'rows':len(equation['residuals']),
            'terms':sum(len(r['terms']) for r in equation['residuals'])}

if __name__=='__main__':
    print(json.dumps([generate(n) for n in ('natural407','integer888','integer917')],indent=2))
