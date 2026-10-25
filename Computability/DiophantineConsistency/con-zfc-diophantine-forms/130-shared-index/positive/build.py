#!/usr/bin/env python3
"""Explore the exact q^3 quotient chart of the pinned ten-positive norm."""
import json,hashlib
from pathlib import Path
from collections import Counter

HERE=Path(__file__).resolve().parent
BASE=HERE/'inherited/gap_fusion'

def build(shifted=False,sharp=False):
    name='gap_fusion_scaled'+('_sharp_centre' if sharp else '')
    parent_path=BASE/'equations'/f'{name}.json'
    p=json.loads(parent_path.read_text())
    rows=[]
    for r in p['source']:
        n,op,x,y=r
        if n=='q2':
            rows.extend([r,['q3','*','q2','q'],['Y','*','q3','s']])
        elif n in ('q3','P1','lowY','q3WBt','inner'):
            continue
        elif n=='P1mu2': rows.append([n,'*','bJ','mu2'])
        elif n=='nV' and not shifted:
            rows.extend([['ns','+','n','s'],[n,'+','ns','V']])
        elif n=='mu2inner': rows.append([n,'*','mu2','B'])
        elif n=='P1e': rows.append([n,'*','bJ','e'])
        elif n=='brk': rows.append([n,'+','mu2inner','P1e'])
        elif n=='Znum': rows.append([n,'-','Zpart1','Zpart2'])
        else: rows.append(r)
    # Topological sorting is needed because Y has become a polynomial input.
    ready=set(['J','F','alpha','i','T','w','s','n','eta','zeta','beta','K0','MC','MF'])
    ordered=[]
    while rows:
        for j,r in enumerate(rows):
            if all(not isinstance(v,str) or v in ready for v in r[2:]):
                ready.add(r[0]);ordered.append(r);rows.pop(j);break
        else: raise ValueError('cyclic rows')
    out=dict(p)
    out['name']='quotient'+('_absorbed' if shifted else '')+('_sharp' if sharp else '')
    out['witnesses']=['s' if v=='Y' else v for v in p['witnesses']]
    out['source']=ordered
    out['operations']=len(ordered)
    out['operation_breakdown']=dict(Counter(r[1] for r in ordered))
    out['exact_degree']=450 if sharp else 466
    degrees={w:1 for w in out['witnesses']}
    for n,op,x,y in ordered:
        dx=degrees.get(x,0) if isinstance(x,str) else 0
        dy=degrees.get(y,0) if isinstance(y,str) else 0
        degrees[n]=dx+dy if op=='*' else max(dx,dy)
    out['syntactic_degree']=degrees[out['output']]
    out['parent']='inherited/gap_fusion/equations/'+parent_path.name
    out['parent_sha256']=hashlib.sha256(parent_path.read_bytes()).hexdigest()
    out['coefficient_binding']={'path':'coefficients/','tuple':'whole original compact44 tuple'}
    out['base']='X=w*q, Y=q^3*s; primitive denominator q-1'
    out['proof']='PROOF.md'
    out['transformation']='Y=q^3*s; divide polynomial by q^12'+('; n_old=n-s' if shifted else '')
    return out

if __name__=='__main__':
    for shifted in (False,True):
        for sharp in (False,True):
            p=build(shifted,sharp)
            (HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=1)+'\n')
            print(p['name'],p['operations'],p['exact_degree'],p['operation_breakdown'])
