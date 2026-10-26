#!/usr/bin/env python3
"""Parse the printed LaTeX residuals independently and compare all terms."""
from pathlib import Path
import json,re

ROOT=Path(__file__).resolve().parent

def parse(path):
    s=path.read_text();out=[]
    blocks=re.findall(r'% BEGIN RESIDUAL (\d+)\n(.*?)% END RESIDUAL (\d+)',s,re.S)
    for index,body,end in blocks:
        if index!=end or int(index)!=len(out):raise ValueError('Residual order')
        body=body.replace(r'\begin{align*}','').replace(r'\end{align*}','')
        prefix='R_{'+index+'} ={}& '
        if prefix not in body:raise ValueError('Missing exact residual prefix')
        body=body.replace(prefix,'',1).replace(r'\\','').replace('&{}','')
        body=re.sub(r'\s+','',body)
        p={}
        for item in re.findall(r'[+-]?[^+-]+',body):
            sign=-1 if item[0]=='-' else 1
            item=item.lstrip('+-')
            c=re.match(r'\d+',item)
            coeff=int(c.group()) if c else 1
            if c:item=item[c.end():]
            mon=[]
            while item:
                m=re.match(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',item)
                if not m:raise ValueError('Unexpected LaTeX token: '+item)
                mon += [int(m.group(1))]*int(m.group(2) or 1)
                item=item[m.end():]
            key=tuple(sorted(mon))
            if key in p:raise ValueError('Duplicate printed monomial')
            p[key]=sign*coeff
        out.append(p)
    return out

def main():
    receipts=[]
    for folder in ['equation','reduced']:
        e=json.loads((ROOT/folder/'equation.json').read_bytes())
        expected=[{tuple(m):c for c,m in r['terms']} for r in e['residuals']]
        actual=parse(ROOT/folder/'residuals.tex')
        if expected!=actual:raise ValueError('Printed residual mismatch: '+folder)
        receipts.append({'profile':folder,'residuals':len(actual),'terms':sum(map(len,actual))})
    if (ROOT/'reduced/residuals.tex').read_bytes()!=(ROOT.parent/'report/quartic212_residuals.tex').read_bytes():
        raise ValueError('Main report appendix differs')
    print(json.dumps({'status':'PASS','printed_equations':receipts},indent=2))

if __name__=='__main__':main()
