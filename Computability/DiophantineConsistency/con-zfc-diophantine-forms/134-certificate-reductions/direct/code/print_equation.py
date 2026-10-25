#!/usr/bin/env python3
"""Emit complete readable and LaTeX versions; --check parses the TeX back."""
from pathlib import Path
from collections import Counter,defaultdict
import argparse,json,re
ROOT=Path(__file__).resolve().parents[1]
def term(c,m,tex=True):
    sign='+' if c>0 else '-';a=abs(c)
    coefficient=str(a) if a!=1 or not m else ''
    factors=[]
    for v,n in sorted(Counter(m).items()):
        s=('z_{'+str(v)+'}') if tex else 'z'+str(v)
        if n>1:s+=('^{'+str(n)+'}') if tex else '^'+str(n)
        factors.append(s)
    return sign+coefficient+('' if tex else '*').join(factors)
def generate():
    eq=json.loads((ROOT/'equation.json').read_text());tex=['% Generated from direct/equation.json; all residuals are printed.','\\begingroup','\\small','\\setlength{\\tabcolsep}{2pt}','\\begin{longtable}{@{}r@{\\;}l@{}}']
    plain=[]
    for j,row in enumerate(eq['residuals']):
        tt=[term(c,m) for c,m in row['terms']]
        if tt[0].startswith('+'):tt[0]=tt[0][1:]
        pp=[term(c,m,False) for c,m in row['terms']]
        if pp[0].startswith('+'):pp[0]=pp[0][1:]
        plain.append('r_'+str(j)+' = '+' '.join(pp))
        for n in range(0,len(tt),3):
            label='\\(r_{'+str(j)+'}=\\)' if n==0 else ''
            tex.append(label+' & \\(\\displaystyle '+ ' '.join(tt[n:n+3])+'\\) \\\\' + ('[3pt]' if n+3>=len(tt) else ''))
    tex+=['\\end{longtable}','\\endgroup','']
    var=['index\tsource_name\tsource_kind']+[f"{i}\t{v['name']}\t{v.get('kind','')}" for i,v in enumerate(eq['variables'])]
    return {'residuals.tex':'\n'.join(tex),'residuals.txt':'\n'.join(plain)+'\n','variables.tsv':'\n'.join(var)+'\n'}
def parse_tex():
    eq=json.loads((ROOT/'equation.json').read_text());groups={};idx=None
    for line in (ROOT/'residuals.tex').read_text().splitlines():
        if '& \\(\\displaystyle ' not in line:continue
        label=re.search(r'r_\{(\d+)\}=',line)
        if label:idx=int(label.group(1));groups[idx]=''
        if idx is None:raise ValueError('Unlabelled first residual')
        rhs=line.split('& \\(\\displaystyle ',1)[1].split('\\)',1)[0]
        groups[idx]+=rhs
    if sorted(groups)!=list(range(len(eq['residuals']))):raise ValueError('TeX residual indices')
    for j,expr in groups.items():
        expr=expr.replace(' ','');parsed=defaultdict(int)
        for token in re.findall(r'[+-]?[^+-]+',expr):
            match=re.fullmatch(r'([+-]?)(\d*)((?:z_\{\d+\}(?:\^\{\d+\})?)*)',token)
            if not match:raise ValueError('Unparsed LaTeX token '+token)
            sign,number,body=match.groups();c=int(number or '1')*(-1 if sign=='-' else 1)
            indices=[]
            for vs,ns in re.findall(r'z_\{(\d+)\}(?:\^\{(\d+)\})?',body):indices += [int(vs)]*int(ns or '1')
            parsed[tuple(sorted(indices))]+=c
        ts=[[c,list(m)] for m,c in sorted(parsed.items()) if c]
        if ts!=eq['residuals'][j]['terms']:raise ValueError('TeX row '+str(j))
    return len(groups)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
    outputs=generate()
    if a.check:
        for name,data in outputs.items():
            if (ROOT/name).read_text()!=data:raise ValueError('Rendered text differs: '+name)
    else:
        for name,data in outputs.items():(ROOT/name).write_text(data)
    print(json.dumps({'status':'PASS','tex_rows_parsed':parse_tex(),'files':list(outputs)}))
