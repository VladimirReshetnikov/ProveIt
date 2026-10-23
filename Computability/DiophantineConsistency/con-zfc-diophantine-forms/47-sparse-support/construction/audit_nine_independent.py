#!/usr/bin/env python3
"""Independent exact degree/identity/liveness audit of sparse nine DAGs.

Uses only Python's standard library. No interpolation or random evaluation
is used. The cancellation-aware DAG is proved equal to the primary DAG by
exact polynomial expansion in nine abstract tail inputs. Its highest total
degree coefficient on the all-variables-equal line is then propagated as
an exact polynomial in every formal fixed leaf. This proves a degree upper
bound and a nonzero attained coefficient for the complete fixed polynomial.
"""
import argparse
import hashlib
import json
from pathlib import Path
from collections import Counter

def require(p, msg):
    if not p: raise ValueError(msg)

def add(p,q,sgn=1):
    out=dict(p)
    for k,v in q.items():
        out[k]=out.get(k,0)+sgn*v
        if not out[k]:del out[k]
    return out

def mul(p,q):
    out={}
    for a,x in p.items():
        for b,y in q.items():
            k=tuple(u+v for u,v in zip(a,b))
            out[k]=out.get(k,0)+x*y
    return {k:v for k,v in out.items() if v}

def const(n,d):return {(0,)*d:n} if n else {}
def variable(i,d):
    v=[0]*d;v[i]=1;return {tuple(v):1}

def ledger(d):
    nodes=d['nodes'];used=set();todo=[d['output']]
    for i,n in enumerate(nodes):
        if n['kind'] in ['add','sub','mul']:
            require(0<=n['left']<i and 0<=n['right']<i,'non-topological DAG')
        else:require(n['kind'] in ['literal','variable','fixed'],'bad node kind')
    while todo:
        i=todo.pop()
        if i in used:continue
        used.add(i);n=nodes[i]
        if 'left' in n:todo += [n['left'],n['right']]
    require(len(used)==len(nodes),'dead node')
    counts=Counter(n['kind'] for n in nodes if 'left' in n)
    require(dict(counts)==d['operation_counts'],'operation ledger mismatch')
    require(sum(counts.values())==d['total_operations'],'total mismatch')
    names=[n['name'] for n in nodes if n['kind']=='variable']
    require(len(names)==9 and set(names)==set(d['variables']),'variable interface')
    return dict(counts)

def hashes(d):
    result=[]
    for n in d['nodes']:
        if 'left' in n:
            args=[result[n['left']],result[n['right']]]
            if n['kind'] in ['add','mul']:args.sort()
            v=[n['kind']]+args
        else:v=[n['kind'],n.get('value',n.get('name'))]
        result.append(hashlib.sha256(json.dumps(v,separators=(',',':')).encode()).hexdigest())
    return result

def ring_tail(d):
    # These common nodes are free indeterminates for a universal ring identity.
    basis=['A','C','E','G','H','E0','Omega','V0','a0'];dim=len(basis)
    cuts={d['named_nodes'][name]:variable(i,dim) for i,name in enumerate(basis)}
    memo={}
    def go(i):
        if i in cuts:return cuts[i]
        if i in memo:return memo[i]
        n=d['nodes'][i];kind=n['kind']
        if kind=='literal':r=const(n['value'],dim)
        elif kind in ['fixed','variable']:raise ValueError('uncut primitive in ring tail')
        else:
            p,q=go(n['left']),go(n['right'])
            r=mul(p,q) if kind=='mul' else add(p,q,1 if kind=='add' else -1)
        memo[i]=r;return r
    result=go(d['output'])
    return result,len(memo)

def exact_degree(d):
    fixed=sorted({n['name'] for n in d['nodes'] if n['kind']=='fixed'})
    dim=len(fixed);which={x:i for i,x in enumerate(fixed)};values=[]
    cancellation=[]
    for i,n in enumerate(d['nodes']):
        k=n['kind']
        if k=='literal':ans=(0,const(n['value'],dim))
        elif k=='fixed':ans=(0,variable(which[n['name']],dim))
        elif k=='variable':ans=(1,const(1,dim))
        else:
            (da,a),(db,b)=values[n['left']],values[n['right']]
            if k=='mul':ans=(da+db,mul(a,b))
            else:
                dd=max(da,db)
                ans=(dd,add(a if da==dd else {},b if db==dd else {},1 if k=='add' else -1))
                if not ans[1] and dd>0:cancellation.append(i)
        values.append(ans)
    deg,lc=values[d['output']];W=d['W'];exp=54148*W+26496
    target=[0]*dim;target[which['base_scale']]=exp
    require(lc=={tuple(target):1<<2050},'unexpected exact symbolic leading form')
    require(deg==108296*W+53272==d['degree'],'degree mismatch')
    # The formal lambda is specialized to the positive power of two in the
    # fixed coefficient binding, so this attained coefficient is nonzero.
    named_degrees={k:values[v][0] for k,v in d['named_nodes'].items()}
    return dict(exact_degree=deg,diagonal_leading_coefficient_power_two=2050,
                diagonal_leading_coefficient_base_scale_exponent=exp,
                canceled_leading_addition_gates=cancellation,named_degree_bounds=named_degrees)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--output',type=Path);args=parser.parse_args();rows=[]
    for p in sorted((args.root/'generated').glob('*nine_*_degree_certificate.json')):
        cert=json.loads(p.read_text());plainpath=p.with_name(p.name.replace('_degree_certificate',''))
        plain=json.loads(plainpath.read_text());lc=ledger(cert);lp=ledger(plain)
        h0,h1=hashes(plain),hashes(cert)
        common=(set(plain['named_nodes'])&set(cert['named_nodes']))-{'inner'}
        for n in common:
            require(h0[plain['named_nodes'][n]]==h1[cert['named_nodes'][n]],'prefix mismatch '+n)
        a,na=ring_tail(plain);b,nb=ring_tail(cert)
        require(a==b,'nonidentical primary and certificate polynomial')
        degree=exact_degree(cert)
        rows.append(dict(primary_file=plainpath.name,certificate_file=p.name,
                         primary_sha256=hashlib.sha256(plainpath.read_bytes()).hexdigest(),
                         certificate_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
                         primary_operations=sum(lp.values()),certificate_operations=sum(lc.values()),
                         all_nodes_live=True,common_named_nodes_checked=len(common),
                         exact_ring_tail_terms=len(a),exact_ring_tail_gates=[na,nb],**degree))
    require(len(rows)==4,'expected four nine-variable variants')
    receipt=dict(method='Exact ring expansion and symbolic highest homogeneous coefficient propagation; no interpolation or sampling.',results=rows)
    encoded=json.dumps(receipt,indent=2)+'\n'
    if args.output:args.output.write_text(encoded)
    print(encoded)

if __name__=='__main__':main()
