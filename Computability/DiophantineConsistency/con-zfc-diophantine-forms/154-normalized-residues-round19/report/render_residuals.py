#!/usr/bin/env python3
"""Render all literal principal residuals, with no algebraic simplification."""
import argparse, json, hashlib
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--equation',type=Path,required=True);p.add_argument('--out',type=Path,default=Path(__file__).with_name('residuals.tex'));a=p.parse_args()
d=json.loads(a.equation.read_text());n=len(d['variables']);m=len(d['residuals'])
def term(c,ids,first):
    counts={i:ids.count(i) for i in sorted(set(ids))}
    mon=''.join('x_{%d}'%i+('^{%d}'%e if e>1 else '') for i,e in counts.items())
    body=('' if abs(c)==1 and mon else str(abs(c)))+mon
    return ('-' if c<0 else ('' if first else '+'))+body
out=[r'\appendix',r'\section{Every residual of the balanced principal equation}',r'\label{sec:residuals}',
     'The following is the complete finite definition of the principal polynomial.',
     r'Its independent coordinates are $x_0,\ldots,x_{%d}\in\Z$, and'% (n-1),
     r'\[P(x_0,\ldots,x_{%d})=\sum_{i=0}^{%d}R_i(x)^2.\]'%(n-1,m-1),
     'Indices are zero based, exactly as in the literal JSON array. No register',
     'or additional quantified variable is implicit in this appendix. The',
     'adjacent collected coefficient file specifies the same polynomial.',
     r'\begingroup\small\setlength{\jot}{1pt}\allowdisplaybreaks[4]',r'\begin{align*}']
for j,row in enumerate(d['residuals']):
    ts=row['terms'];chunks=[ts[i:i+6] for i in range(0,len(ts),6)]
    for k,ch in enumerate(chunks):
        prefix=('R_{%d}&='%j) if k==0 else r'&\quad{}'
        out.append(prefix+''.join(term(c,ids,k==0 and z==0) for z,(c,ids) in enumerate(ch))+r'\\')
out += [r'\end{align*}',r'\endgroup','']
a.out.write_text('\n'.join(out))
print(json.dumps({'residuals':m,'variables':n,'source_sha256':hashlib.sha256(a.equation.read_bytes()).hexdigest(),'tex_sha256':hashlib.sha256(a.out.read_bytes()).hexdigest()},sort_keys=True))
