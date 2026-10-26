#!/usr/bin/env python3
"""Export readable residuals and the complete literal LaTeX appendix."""
from pathlib import Path
from collections import Counter
import json

ROOT=Path(__file__).resolve().parent

def term(c,m,tex=False,first=False):
    sign=('-' if c<0 else '') if first else (' - ' if c<0 else ' + ')
    factors=[]
    for i,k in sorted(Counter(m).items()):
        if tex:factors.append('x_{'+str(i)+'}'+('^{'+str(k)+'}' if k>1 else ''))
        else:factors.append('x'+str(i)+('^'+str(k) if k>1 else ''))
    coeff=str(abs(c)) if abs(c)!=1 or not m else ''
    if tex:return sign+coeff+' '.join(factors)
    return sign+coeff+('*' if coeff and factors else '')+'*'.join(factors)

def export(profile):
    folder=ROOT/profile;e=json.loads((folder/'equation.json').read_bytes())
    text=['Domain: all 212 variables are independent unrestricted integers.',
          'P(x0,...,x211) = R0^2 + ... + R151^2. The equation is P=0.','']
    tex=[r'{\small',r'\setlength{\jot}{2pt}',r'\allowdisplaybreaks[2]']
    for j,r in enumerate(e['residuals']):
        ts=sorted(r['terms'],key=lambda x:x[1])
        text.append('R'+str(j)+' = '+''.join(term(c,m,first=i==0) for i,(c,m) in enumerate(ts)))
        tex += ['% BEGIN RESIDUAL '+str(j),r'\begin{align*}']
        for start in range(0,len(ts),5):
            expr=''.join(term(c,m,tex=True,first=start+i==0) for i,(c,m) in enumerate(ts[start:start+5]))
            pref='R_{'+str(j)+'} ={}& ' if start==0 else '&{} '
            tex.append(pref+expr+(r' \\' if start+5<len(ts) else ''))
        tex += [r'\end{align*}','% END RESIDUAL '+str(j)]
    tex.append('}')
    (folder/'residuals.txt').write_text('\n'.join(text)+'\n')
    (folder/'residuals.tex').write_text('\n'.join(tex)+'\n')
    (folder/'variables.tsv').write_text('index\tname\n'+''.join(str(i)+'\t'+v['name']+'\n' for i,v in enumerate(e['variables'])))
    if profile=='reduced':(ROOT.parent/'report/quartic212_residuals.tex').write_text('\n'.join(tex)+'\n')
    return {'profile':profile,'residuals':len(e['residuals']),'printed_terms':sum(len(r['terms']) for r in e['residuals'])}

if __name__=='__main__':print(json.dumps([export(p) for p in ['equation','reduced']],indent=2))
