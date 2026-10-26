#!/usr/bin/env python3
"""Greedy exact integral row reduction with an elementary operation ledger."""
from pathlib import Path
import argparse, copy, hashlib, json
from build import canonical, collect, square_sum, terms


def dot(p,q):
    if len(p)>len(q): p,q=q,p
    return sum(c*q.get(m,0) for m,c in p.items())


def submul(p,q,k):
    out=p.copy()
    for m,c in q.items():
        out[m]=out.get(m,0)-k*c
        if not out[m]: del out[m]
    return out


def run(source,destination):
    raw=source.read_bytes(); old=json.loads(raw)
    rows=[collect(r['terms']) for r in old['residuals']]
    norms=[dot(r,r) for r in rows]
    ledger=[]
    while True:
        best=None
        for i,p in enumerate(rows):
            for j,q in enumerate(rows):
                if i==j or norms[j]==0: continue
                prod=dot(p,q)
                floor=prod//norms[j]
                for k in {floor,floor+1}:
                    if not k: continue
                    newnorm=norms[i]-2*k*prod+k*k*norms[j]
                    saving=norms[i]-newnorm
                    if saving>0 and (best is None or saving>best[0]):
                        best=(saving,i,j,k,newnorm)
        if best is None: break
        saving,i,j,k,newnorm=best
        rows[i]=submul(rows[i],rows[j],k)
        norms[i]=newnorm
        ledger.append({'target':i,'source':j,'multiple':-k})
    e=copy.deepcopy(old)
    for r,p in zip(e['residuals'],rows):r['terms']=terms(p)
    e['variant'] += ':reduced_row_basis'
    e['row_basis_parent_sha256']=hashlib.sha256(raw).hexdigest()
    expansion=square_sum(e['residuals'])
    maximum=max(map(abs,expansion.values()))
    metrics={'variables':len(e['variables']),'residuals':len(e['residuals']),
             'degree':max(map(len,expansion)), 'monomials':len(expansion),
             'coefficient_height':maximum,
             'residual_height':max(abs(c) for p in rows for c in p.values()),
             'residual_monomials':sum(map(len,rows)),
             'height_witnesses':[[c,list(m)] for m,c in expansion.items() if abs(c)==maximum],
             'domain':'unrestricted integers',
             'basis_operations':len(ledger)}
    cert={'schema':'integral-residual-row-operations-v1',
          'input_sha256':hashlib.sha256(raw).hexdigest(),
          'output_sha256':hashlib.sha256(canonical(e)).hexdigest(),
          'operations':ledger,
          'inverse':'Reverse the operation order and negate every multiple.'}
    destination.mkdir(parents=True,exist_ok=True)
    for name,obj in [('equation.json',e),('metrics.json',metrics),('basis_certificate.json',cert),
                     ('expanded_polynomial.json',{'schema':'sparse-polynomial-v1','variables':len(e['variables']),'terms':terms(expansion)})]:
        (destination/name).write_bytes(canonical(obj))
    return metrics


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();print(json.dumps(run(a.source,a.output),indent=2))
