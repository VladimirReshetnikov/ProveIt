#!/usr/bin/env python3
"""Independent exact recurrence and polynomial-assembly audit; no builder imports."""
import argparse,collections,hashlib,json
from pathlib import Path

def demand(test,message):
    if not test:raise ValueError(message)

def add(p,q,scale=1):
    r=dict(p)
    for m,c in q.items():
        r[m]=r.get(m,0)+scale*c
        if not r[m]:del r[m]
    return r

def mul(p,q):
    r={}
    for m,c in p.items():
        for n,d in q.items():
            key=tuple(sorted(m+n));r[key]=r.get(key,0)+c*d
    return {m:c for m,c in r.items() if c}

def const(c):return {():c} if c else {}
def scale(p,c):return {m:v*c for m,v in p.items() if v*c}

def audit(folder):
    raw=json.loads((folder/'semantic_certificate.json').read_text())
    ns=raw['nodes'];batch=raw['batch']
    A={(0,):1};X={(1,):1};Y={(2,):1};one=const(1)
    D=add(mul(A,A),one,-1)
    generic=[(X,Y)]
    generic.append((add(mul(A,X),mul(D,Y)),add(X,mul(A,Y))))
    generic.append((add(scale(mul(A,generic[1][0]),2),X,-1),
                    add(scale(mul(A,generic[1][1]),2),Y,-1)))
    def norm(x,y):return add(mul(x,x),mul(D,mul(y,y)),-1)
    for shift in (1,2):demand(norm(*generic[shift])==norm(X,Y),'free recurrence norm identity')
    direct2=(add(mul(add(scale(mul(A,A),2),one,-1),X),scale(mul(mul(A,D),Y),2)),
             add(scale(mul(A,X),2),mul(add(scale(mul(A,A),2),one,-1),Y)))
    demand(generic[2]==direct2,'second order versus direct double shift')
    def polynomial_at(root,cuts):
        memo={}
        def go(i):
            if i in cuts:return cuts[i]
            if i in memo:return memo[i]
            n=ns[i]
            if n[0]=='c':p=const(n[1])
            elif n[0]=='a':p=add(go(n[1]),go(n[2]))
            elif n[0]=='s':p=add(go(n[1]),go(n[2]),-1)
            elif n[0]=='m':p=mul(go(n[1]),go(n[2]))
            else:raise ValueError('unexpected dependency under recurrence cut')
            memo[i]=p;return p
        return go(root)
    # Build exact affine forms in sparse nonlinear atoms by independent scan.
    affine=[]
    for i,n in enumerate(ns):
        if n[0]=='c':p=const(n[1])
        elif n[0] in ('a','s'):p=add(affine[n[1]],affine[n[2]],1 if n[0]=='a' else -1)
        elif n[0]=='m' and ns[n[1]][0]=='c':p=scale(affine[n[2]],ns[n[1]][1])
        elif n[0]=='m' and ns[n[2]][0]=='c':p=scale(affine[n[1]],ns[n[2]][1])
        else:p={(i,):1}
        affine.append(p)
    seeds={j['k']:j for j in batch['seed_indices']}
    derived=[j for j in batch['indices'] if j['certificate']=='recurrence']
    demand(len(seeds)==16 and len(derived)==3 and len(batch['indices'])==19,'actual index counts')
    seen=[]
    for j in derived:
        par=seeds[j['parent_exponent']];shift=j['shift']
        demand(shift in (1,2),'proved shift scope')
        demand(add(affine[j['k']],affine[par['k']],-1)==const(shift),'exact exponent difference')
        cuts={batch['A']:A,par['X']:X,par['Y']:Y}
        demand(polynomial_at(j['X'],cuts)==generic[shift][0],'complete X recurrence DAG')
        demand(polynomial_at(j['Y'],cuts)==generic[shift][1],'complete Y recurrence DAG')
        seen.append({'tag':j['tag'],'parent_tag':par['tag'],'shift':shift})
    # P must be a product of precisely the seed ordinates, not a lossy subset.
    symbols={j['Y']:{(q,):1} for q,j in enumerate(seeds.values())}
    demand(polynomial_at(batch['P'],symbols)=={tuple(range(16)):1},'complete seed ordinate product')
    # The output file is exactly the SOS of all delivered quadratic residuals.
    rows=json.loads((folder/'residuals.json').read_text())
    output=json.loads((folder/'polynomial.json').read_text())
    sums={}
    for row in rows:
        terms=row['terms']; p={tuple(m):c for c,m in terms}
        demand(len(p)==len(terms),'duplicate residual monomial')
        demand(all(len(m)<=2 and c for m,c in p.items()),'quadratic residual support')
        sums=add(sums,mul(p,p))
    full={tuple(m):c for c,m in output['terms']}
    demand(len(full)==len(output['terms']),'duplicate final monomial')
    demand(full==sums,'entire sparse SOS identity')
    n=output['variable_count'];used={j for mon in full for j in mon}
    demand(used==set(range(n)),'all final variables live')
    demand(max(map(len,full))==4,'exact quartic degree')
    stats={'variable_count':n,'residual_count':len(rows),'monomial_count':len(full),
           'exact_degree':4,'coefficient_height':max(abs(c) for c in full.values())}
    # A degree/operation-preserving wrong coefficient is rejected exactly.
    broken=dict(full);first=next(iter(broken));broken[first]+=1
    demand(broken!=sums,'coefficient mutation control')
    hashes={f:hashlib.sha256((folder/f).read_bytes()).hexdigest() for f in
            ('semantic_certificate.json','residuals.json','polynomial.json')}
    return {'status':'PASS','scope':'exact recurrence equations and full SOS assembly; not a full source-semantic proof',
            'recurrence_relations':seen,'seed_count':16,'distinct_exponent_count':19,
            'metrics':stats,'sha256':hashes,'mutation_control':'changed final coefficient rejected'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--equations',type=Path,default=Path(__file__).parent/'equations')
    p.add_argument('--output',type=Path,default=Path(__file__).parent/'RECURRENCE_INDEPENDENT_CHECKS.json')
    args=p.parse_args();r=audit(args.equations);args.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
