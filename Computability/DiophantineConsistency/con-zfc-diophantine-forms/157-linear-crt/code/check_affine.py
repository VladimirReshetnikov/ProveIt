#!/usr/bin/env python3
"""Read-only, independent checker for affine projection endpoints.

Usage: python3 -B check_affine.py SOURCE_EQUATION_JSON ENDPOINT_DIRECTORY
No producer module, external package, assertion statement, or network needed.
"""
from pathlib import Path
from collections import defaultdict
import argparse, hashlib, json

def require(condition, description):
    if not condition:
        raise ValueError(description)

def decode(terms):
    out={}
    for c,m in terms:
        require(isinstance(c,int) and c!=0,'nonzero integer coefficient')
        mm=tuple(m)
        require(tuple(sorted(m))==mm,'ordered monomial')
        require(mm not in out,'unique monomial')
        out[mm]=c
    return out

def encode(p):
    return [[c,list(m)] for m,c in sorted(p.items()) if c]

def add(a,b,k=1):
    r=dict(a)
    for m,c in b.items():
        r[m]=r.get(m,0)+k*c
        if not r[m]:
            del r[m]
    return r

def multiply(a,b):
    r=defaultdict(int)
    for m,c in a.items():
        for n,d in b.items():
            r[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in r.items() if c}

def substitute(p,i,q):
    result={}
    for m,c in p.items():
        term={():c}
        for j in m:
            term=multiply(term,q if j==i else {(j,):1})
        result=add(result,term)
    return result

def compose(p,coordinates):
    result={}
    for m,c in p.items():
        term={():c}
        for i in m:
            term=multiply(term,coordinates[i])
        result=add(result,term)
    return result

def check(source_path, directory):
    source_bytes=source_path.read_bytes()
    source=json.loads(source_bytes)
    certificate=json.loads((directory/'certificate.json').read_bytes())
    equation=json.loads((directory/'equation.json').read_bytes())
    expansion=json.loads((directory/'expanded_polynomial.json').read_bytes())
    restoration=json.loads((directory/'RESTORATION.json').read_bytes())
    metric=json.loads((directory/'METRICS.json').read_bytes())
    require(hashlib.sha256(source_bytes).hexdigest()==certificate['source_sha256'],'source hash')
    variables=source['variables']
    names={v['name']:i for i,v in enumerate(variables)}
    require(len(names)==len(variables),'unique source names')
    original=[decode(r['terms']) for r in source['residuals']]
    rows=[dict(r) for r in original]
    maps=[{(i,):1} for i in range(len(variables))]
    for target,inputs in certificate['coordinate_shears']:
        i=names[target]
        require(target not in inputs,'invertible elementary coordinate shear')
        q={(i,):1}
        for name,c in inputs.items():
            require(isinstance(c,int),'integer shear coefficient')
            q=add(q,{(names[name],):c})
        rows=[substitute(r,i,q) for r in rows]
        maps=[substitute(p,i,q) for p in maps]
    def row_operations(target, operations, inverse=False):
        for i,j,k in reversed(operations) if inverse else operations:
            require(i!=j and 0<=i<len(target) and 0<=j<len(target),'elementary row indices')
            require(isinstance(k,int),'integer row coefficient')
            target[i]=add(target[i],target[j],-k if inverse else k)
    row_operations(rows,certificate['row_operations'])
    removed_rows=[]
    removed_vars=[]
    for pivot in certificate['projections']:
        row,i=pivot['row'],pivot['variable']
        require(names[pivot['name']]==i,'pivot name and index')
        require(row not in removed_rows and i not in removed_vars,'unique pivot')
        q=decode(pivot['replacement'])
        require(not any(i in m for m in q),'pivot independent of its variable')
        require(max(map(len,q),default=0)<=1,'affine restoration')
        coefficient=rows[row].get((i,),0)
        require(coefficient in(-1,1),'unit pivot coefficient')
        require(rows[row]==add({(i,):coefficient},q,-coefficient),'literal unit affine row')
        rows=[substitute(r,i,q) for r in rows]
        maps=[substitute(p,i,q) for p in maps]
        require(not rows[row],'pivot vanishes identically')
        removed_rows.append(row)
        removed_vars.append(i)
    keep=[i for i in range(len(variables)) if i not in removed_vars]
    ren={i:j for j,i in enumerate(keep)}
    def renumber(p):
        require(all(i in ren for m in p for i in m),'removed coordinates absent')
        return {tuple(ren[i] for i in m):c for m,c in p.items()}
    rows=[renumber(r) for i,r in enumerate(rows) if i not in removed_rows]
    maps=[renumber(p) for p in maps]
    row_operations(rows,certificate['final_row_operations'])
    require(equation['variables']==[variables[i] for i in keep],'ordered endpoint variables')
    actual_rows=[decode(r['terms']) for r in equation['residuals']]
    require(rows==actual_rows,'every endpoint coefficient')
    require(restoration['retained_source_coordinates']==keep,'restoration kept coordinates')
    require([encode(p) for p in maps]==restoration['source_in_target_coordinates'],'every restoration coefficient')
    reverse=[dict(r) for r in actual_rows]
    row_operations(reverse,certificate['final_row_operations'],inverse=True)
    ri=iter(reverse)
    reverse=[{} if i in removed_rows else next(ri) for i in range(len(original))]
    row_operations(reverse,certificate['row_operations'],inverse=True)
    require(reverse==[compose(r,maps) for r in original],'every source residual pullback')
    polynomial={}
    for row in actual_rows:
        require(max(map(len,row),default=0)<=2,'quadratic residual')
        polynomial=add(polynomial,multiply(row,row))
    require(polynomial==decode(expansion['terms']),'complete quartic expansion')
    require({i for m in polynomial for i in m}==set(range(len(keep))),'all variables genuinely occur')
    measured={'variables':len(keep),'rows':len(rows),'degree':max(map(len,polynomial)),
              'monomials':len(polynomial),'height':max(map(abs,polynomial.values())),
              'row_height':max(abs(c) for r in rows for c in r.values()),'row_support':sum(map(len,rows))}
    require(measured==metric,'all metrics')
    return {'source_sha256':certificate['source_sha256'],'result':measured,
            'checked_source_pullbacks':len(original),'inverse_row_operations':len(certificate['row_operations'])+len(certificate['final_row_operations']),
            'affine_projections':len(removed_rows),'coordinate_shears':len(certificate['coordinate_shears'])}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path)
    parser.add_argument('endpoint',type=Path)
    args=parser.parse_args()
    print(json.dumps(check(args.source,args.endpoint),indent=2,sort_keys=True))
