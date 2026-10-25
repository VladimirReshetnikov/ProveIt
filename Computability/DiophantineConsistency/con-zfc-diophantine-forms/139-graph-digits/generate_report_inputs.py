#!/usr/bin/env python3
"""Bind the printed literal appendices to the delivered mathematical JSON."""
from collections import Counter
from pathlib import Path
import argparse
import json

ROOT=Path(__file__).resolve().parent

def sources():
    eq=json.loads((ROOT/'direct/equations/natural226/equation.json').read_text())
    if len(eq['variables'])!=226 or len(eq['residuals'])!=175:raise ValueError('Wrong principal equation')
    lines=['% Generated from direct/equations/natural226/equation.json.',r'\begingroup\small',r'\allowdisplaybreaks']
    for j,row in enumerate(eq['residuals']):
        out=[]
        for coef,mon in row['terms']:
            text='-' if coef<0 else '+'
            a=abs(coef)
            if a!=1 or not mon:text+=str(a)
            for var,count in sorted(Counter(mon).items()):
                text+=r'z_{'+str(var)+'}'
                if count>1:text+='^{'+str(count)+'}'
            out.append(text)
        chunks=[''.join(out[k:k+6]) for k in range(0,len(out),6)]
        if chunks[0].startswith('+'):chunks[0]=chunks[0][1:]
        lines.append(r'\[\begin{aligned}Q_{'+str(j)+'}={}&'+chunks[0])
        for chunk in chunks[1:]:lines.append(r'\\&'+chunk)
        lines.append(r'\end{aligned}\]')
    lines.append(r'\endgroup')
    natural='\n'.join(lines)+'\n'
    circuit=json.loads((ROOT/'compact/equation_87_degree323.json').read_text())
    if len(circuit['source'])!=87:raise ValueError('Wrong compact operation count')
    tex=[r'\begingroup\small',r'\begin{longtable}{@{}rll@{}}',r'\toprule Step & Register & Binary definition\\\midrule\endhead']
    def tt(x):return r'\texttt{'+str(x).replace('_',r'\_')+'}'
    for k,(name,op,a,b) in enumerate(circuit['source'],1):
        tex.append(str(k)+' & '+tt(name)+' & '+tt(a)+' '+tt(op)+' '+tt(b)+r'\\')
    tex += [r'\bottomrule\end{longtable}',r'\endgroup']
    recipe=(ROOT/'compact/construct_coefficients.py').read_text()
    recipe=recipe[:recipe.index('\ndef raw_bytes')].rstrip()+'\n'
    return {'natural226_residuals.tex':natural,'compact_registers.tex':'\n'.join(tex)+'\n','constant_recipe.py':recipe}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');a=p.parse_args()
    for name,text in sources().items():
        path=ROOT/'report_inputs'/name
        if a.check:
            if path.read_text()!=text:raise ValueError('Printed appendix differs: '+name)
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
    print('Printed appendices: '+('verified' if a.check else 'generated'))

if __name__=='__main__':main()
