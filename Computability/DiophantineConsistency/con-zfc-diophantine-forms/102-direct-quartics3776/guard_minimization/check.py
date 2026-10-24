#!/usr/bin/env python3
"""Independent certificate checker. Imports no builder or optimizer.

Checks universal polynomial identities/sign implications, not sample zeros.
"""
from collections import defaultdict,Counter
from hashlib import sha256
from pathlib import Path
import json
import argparse

HERE=Path(__file__).resolve().parent

def need(condition,message):
    if not condition:raise ValueError(message)

def sparse(terms):
    out=defaultdict(int)
    for c,m in terms:out[tuple(sorted(m))]+=c
    return {m:c for m,c in out.items() if c}

def shift(poly,bounds):
    """Substitute X_i=T_i+L_i only when a nonnegative L_i is proved."""
    result=defaultdict(int)
    for monomial,coefficient in poly.items():
        terms={():coefficient}
        for i in monomial:
            following=defaultdict(int)
            for m,c in terms.items():
                following[tuple(sorted(m+(i,)))]+=c
                if bounds[i]>0:following[m]+=c*bounds[i]
            terms=following
        for m,c in terms.items():result[m]+=c
    return {m:c for m,c in result.items() if c}

def nonnegative(poly,bounds,strict=False):
    changed=shift(poly,bounds)
    if any(c<0 for c in changed.values()):return False
    for m in changed:
        if any(e%2 and bounds[i]<0 for i,e in Counter(m).items()):return False
    return not strict or changed.get((),0)>0

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--source',type=Path,default=HERE.parent/'signed_quotients/candidate/equation.json')
    parser.add_argument('--candidate',type=Path,default=HERE/'candidate')
    args=parser.parse_args();folder=args.candidate
    raw=args.source.read_bytes()
    source=json.loads(raw)
    cert=json.loads((folder/'guard_certificate.json').read_text())
    eq=json.loads((folder/'equation.json').read_text())
    target_poly=json.loads((folder/'expanded_polynomial.json').read_text())
    need(source['domain']==eq['domain']==target_poly['domain']=='unrestricted integers','wrong domain')
    need(sha256(raw).hexdigest()==cert['source_sha256']==eq['source_6628_sha256'],'source hash')
    nc=source['metrics']['core_variables'];nr=source['metrics']['core_rows']
    need((nc,nr)==(cert['core_variables'],cert['core_rows']),'core counts')
    variables=source['variables'][:nc];rows=source['residuals'][:nr]
    for row in rows:
        need(all(type(c) is int and c!=0 and all(type(i) is int and 0<=i<nc for i in m) and len(m)<=2 for c,m in row['terms']),'invalid core term')
        need(len(sparse(row['terms']))==len(row['terms']),'noncanonical core row')
    need(eq['variables'][:nc]==variables and eq['residuals'][:nr]==rows,'core changed')
    natural={i for i,v in enumerate(variables) if v['kind']!='signed_quotient'}
    semantic={i for i,v in enumerate(variables) if v['kind'] in ('outer','witness')}
    guards=cert['guarded_coordinates'];need(len(set(guards))==len(guards),'duplicate guard')
    need(set(guards)<=semantic,'guard target not semantic')
    normalized=set()
    for generator in cert['sign_symmetries']:
        pivot=generator['normalized_variable'];flips=set(generator['flip_variables'])
        need(len(flips)==len(generator['flip_variables']),'duplicate sign coordinate')
        need(all(0<=i<nc for i in flips),'bad sign coordinate')
        need(flips&semantic=={pivot},'sign generator changes another semantic coordinate')
        need(pivot not in guards and pivot not in normalized,'normalization pivot conflict')
        normalized.add(pivot)
        for j,row in enumerate(rows):
            parities={sum(i in flips for i in m)%2 for c,m in row['terms'] if c}
            need(len(parities)==1,f'not a diagonal row automorphism: {pivot}/{j}')
    bounds=[-1]*nc
    for i in set(guards)|normalized:bounds[i]=0
    for n,step in enumerate(cert['bound_derivations']):
        x=step['variable'];new=step['lower_bound'];j=step['row']
        need(type(x) is int and type(j) is int and type(new) is int and new in (0,1,2),f'bad step types {n}')
        need(x in natural and 0<=j<nr and bounds[x]<new,f'bad step {n}')
        A=defaultdict(int);B=defaultdict(int)
        for c,m in rows[j]['terms']:
            count=m.count(x)
            need(count<=1,f'nonlinear target at step {n}')
            if count:A[tuple(i for i in m if i!=x)]+=c
            else:B[tuple(m)]-=c
        A={m:c for m,c in A.items() if c};B={m:c for m,c in B.items() if c}
        need(A,f'no target at step {n}')
        if all(c<0 for c in A.values()):A={m:-c for m,c in A.items()};B={m:-c for m,c in B.items()}
        need(nonnegative(A,bounds,True),f'factor not strictly positive at step {n}')
        if new==0:need(nonnegative(B,bounds),f'RHS not nonnegative at step {n}')
        elif new==1:need(nonnegative(B,bounds,True),f'RHS not positive at step {n}')
        elif new==2:
            delta=defaultdict(int,B)
            for m,c in A.items():delta[m]-=c
            need(nonnegative(dict(delta),bounds,True),f'RHS-factor not positive at step {n}')
        bounds[x]=new
    need(bounds==cert['final_lower_bounds'],'final bounds mismatch')
    need(all(bounds[i]>=0 for i in natural),'natural coordinate not recovered')
    need(all(bounds[i]==-1 for i in set(range(nc))-natural),'signed quotient unexpectedly bounded')
    need(len(eq['natural_input_guards'])==len(guards),'guard count')
    next_var=nc
    for k,i in enumerate(guards):
        a,b,c=next_var,next_var+1,next_var+2;next_var+=3
        need(eq['natural_input_guards'][k]=={'input':i,'auxiliaries':[a,b,c]},'guard metadata')
        expected={(i,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}
        need(sparse(eq['residuals'][nr+k]['terms'])==expected,'guard residual')
        for q,suffix in zip((a,b,c),'abc'):
            need(eq['variables'][q]=={'kind':'guard_auxiliary','name':f'nat.{i}.{suffix}'},'guard variable')
    need(len(eq['residuals'])==nr+len(guards) and len(eq['variables'])==next_var,'extra rows or variables')
    expansion=defaultdict(int)
    for j,row in enumerate(eq['residuals']):
        need(all(type(c) is int and c!=0 and all(type(i) is int and 0<=i<next_var for i in m) and len(m)<=2 for c,m in row['terms']),f'bad row {j}')
        terms=list(sparse(row['terms']).items())
        for a,(m,c) in enumerate(terms):
            for n,d in terms[a:]:expansion[tuple(sorted(m+n))]+=c*d*(1 if n==m else 2)
    expansion={m:c for m,c in expansion.items() if c}
    need(all(type(c) is int and c!=0 and m==sorted(m) and all(type(i) is int and 0<=i<next_var for i in m) for c,m in target_poly['terms']),'bad expanded term')
    need(expansion==sparse(target_poly['terms']),'expanded polynomial mismatch')
    need(len(target_poly['terms'])==len(expansion),'duplicate expanded monomials')
    need(target_poly['variables']==next_var,'expanded dimension')
    used={i for m in expansion for i in m};need(used==set(range(next_var)),'dead final variable')
    degree=max(map(len,expansion));height=max(map(abs,expansion.values()))
    measured={'variables':next_var,'quadratic_rows':len(eq['residuals']),'exact_degree':degree,
              'expanded_monomials':len(expansion),'coefficient_height':height,
              'guarded_coordinates':len(guards),'sign_normalized_coordinates':len(normalized),
              'inferred_semantic_coordinates':len(semantic)-len(guards)-len(normalized),
              'bound_derivation_steps':len(cert['bound_derivations'])}
    need(all(eq['metrics'][k]==v for k,v in measured.items()),'declared metrics mismatch')
    receipt={'status':'PASS','scope':'Exact row automorphisms, ordered sign implications, guard identities, full quartic expansion and liveness',
             'metrics':measured,'source_sha256':sha256(raw).hexdigest(),
             'equation_sha256':sha256((folder/'equation.json').read_bytes()).hexdigest()}
    print(json.dumps(receipt,sort_keys=True,indent=2))

if __name__=='__main__':main()
