#!/usr/bin/env python3
"""Write exact readable residuals and variable maps from the selected JSON."""
from pathlib import Path
from collections import Counter
import argparse,json
ROOT=Path(__file__).resolve().parent
ENDPOINTS=['factorial_free_affine242_balanced','factorial_free_affine241_balanced']

def atom(m,tex=False):
    counts=Counter(m);out=[]
    for v,e in sorted(counts.items()):
        x=f'x_{{{v}}}'if tex else f'x{v}'
        if e!=1:x+=(f'^{{{e}}}'if tex else f'**{e}')
        out.append(x)
    return (' 'if tex else '*').join(out)
def signed(c,m,tex=False,first=False):
    body=atom(m,tex)
    if not body:body=str(abs(c))
    elif abs(c)!=1:body=str(abs(c))+('\\,'if tex else '*')+body
    if c<0:return '-'+body
    return (''if first else '+')+body

def exports(folder):
    eq=json.loads((folder/'equation.json').read_text());plain=[];latex=['% Generated exactly from equation.json; zero-based variable indices.','\\begin{align*}']
    for j,row in enumerate(eq['residuals']):
        ts=row['terms'];plain.append(f'R{j} = '+' '.join(signed(c,m,first=k==0)for k,(c,m)in enumerate(ts)))
        chunks=[];line=[];size=0
        for k,(c,m)in enumerate(ts):
            term=signed(c,m,True,k==0);cost=len(term)+1
            if line and size+cost>104:chunks.append(' '.join(line));line=[];size=0
            line.append(term);size+=cost
        if line:chunks.append(' '.join(line))
        for k,text in enumerate(chunks):
            prefix=f'R_{{{j}}} &={{}} 'if k==0 else '&\\quad{} '
            suffix=' \\\\[2pt]'if k==len(chunks)-1 and j<len(eq['residuals'])-1 else ' \\\\'if k<len(chunks)-1 else ''
            latex.append(prefix+text+suffix)
    latex+=['\\end{align*}','']
    variables=['index\tname\tkind']+[f"{i}\t{v['name']}\t{v.get('kind','')}"for i,v in enumerate(eq['variables'])]
    return {'residuals.txt':'\n'.join(plain)+'\n','residuals.tex':'\n'.join(latex),'variables.tsv':'\n'.join(variables)+'\n'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();count=0
    for name in ENDPOINTS:
        folder=ROOT/name
        for filename,text in exports(folder).items():
            path=folder/filename
            if a.check:
                if path.read_text()!=text:raise ValueError('Export differs: '+str(path))
            else:path.write_text(text)
            count+=1
    print(json.dumps({'status':'PASS','readable_files':count,'mode':'check'if a.check else'write'}))

if __name__=='__main__':main()
