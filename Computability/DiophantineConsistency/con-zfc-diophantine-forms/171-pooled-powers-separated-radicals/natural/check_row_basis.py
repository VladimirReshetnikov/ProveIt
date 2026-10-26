#!/usr/bin/env python3
"""Independent exact verifier for elementary residual-basis certificates."""
import argparse, json, hashlib
from collections import defaultdict
from pathlib import Path

def require(b,m):
    if not b: raise ValueError(m)
def decode(rows,n):
    out=[]
    for row in rows:
        p={}
        for c,m in row['terms']:
            require(type(c) is int and c!=0,'coefficient')
            require(all(type(i) is int and 0<=i<n for i in m),'coordinate')
            k=tuple(m);require(tuple(sorted(k))==k and k not in p,'canonical monomial')
            p[k]=c
        out.append(p)
    return out

def add(a,b,k):
    c=dict(a)
    for m,v in b.items():
        c[m]=c.get(m,0)+k*v
        if c[m]==0: del c[m]
    return c

def expand(rows):
    p=defaultdict(int)
    for row in rows:
        for a,c in row.items():
            for b,d in row.items():p[tuple(sorted(a+b))]+=c*d
    return {m:c for m,c in p.items() if c}

def verify(source,cert):
    n=len(source['variables']); original=decode(source['residuals'],n)
    require(cert['equation']['variables']==source['variables'],'variable identity')
    rows=[dict(r) for r in original]
    for i,j,k in cert['operations']:
        require(all(type(x) is int for x in (i,j,k)),'integral operation')
        require(0<=i<len(rows) and 0<=j<len(rows) and i!=j and k!=0,'elementary shear')
        rows[i]=add(rows[i],rows[j],k)
    target=decode(cert['equation']['residuals'],n)
    require(rows==target,'forward exact rows')
    back=[dict(r) for r in target]
    for i,j,k in reversed(cert['operations']):back[i]=add(back[i],back[j],-k)
    require(back==original,'inverse exact rows')
    p=expand(target)
    require(p and max(map(len,p))==4,'exact quartic')
    live=set(i for m in p for i in m)
    require(live==set(range(n)),'all coordinates live')
    metrics=dict(variables=n,rows=len(rows),terms=len(p),height=max(abs(c) for c in p.values()),row_height=max(abs(c) for r in rows for c in r.values()),row_support=sum(map(len,rows)))
    require(metrics==cert['metrics'],'full metrics')
    lead=next((m,c) for m,c in sorted(p.items()) if len(m)==4)
    return metrics,lead,p

def main():
    a=argparse.ArgumentParser();a.add_argument('source');a.add_argument('certificate');a.add_argument('--output');args=a.parse_args()
    source=json.loads(Path(args.source).read_text());cert=json.loads(Path(args.certificate).read_text())
    metrics,lead,p=verify(source,cert)
    rejected=[]
    mutations=[]
    c=json.loads(json.dumps(cert));c['operations'][0][2]+=1;mutations.append(('wrong multiplier',c))
    c=json.loads(json.dumps(cert));c['equation']['residuals'][0]['terms'][0][0]+=1;mutations.append(('wrong residual',c))
    c=json.loads(json.dumps(cert));c['operations'][0][1]=c['operations'][0][0];mutations.append(('singular replacement',c))
    c=json.loads(json.dumps(cert));c['equation']['residuals'].pop();mutations.append(('missing row',c))
    c=json.loads(json.dumps(cert));c['metrics']['height']+=1;mutations.append(('wrong height',c))
    for label,c in mutations:
        try:verify(source,c)
        except (ValueError,IndexError):rejected.append(label)
        else:raise ValueError('mutation accepted '+label)
    result={'status':'PASS','metrics':metrics,'exact_degree_witness':[lead[1],list(lead[0])],'elementary_shears':len(cert['operations']),'negative_controls':rejected,'source_sha256':hashlib.sha256(Path(args.source).read_bytes()).hexdigest(),'certificate_sha256':hashlib.sha256(Path(args.certificate).read_bytes()).hexdigest(),'scope':'Finite exact algebra; residual systems are equivalent by explicit inverse row maps; sums of squares have the same zeros over the stated integer or natural domain.'}
    if args.output:Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
