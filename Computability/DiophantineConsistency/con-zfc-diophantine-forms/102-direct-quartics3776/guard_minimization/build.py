#!/usr/bin/env python3
"""Materialize a guard-reduced quartic and its finite symbolic certificate."""
from collections import defaultdict
from hashlib import sha256
import json
import argparse
from pathlib import Path
from copy import deepcopy

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'signed_quotients/candidate/equation.json'

def require(ok,msg):
    if not ok: raise ValueError(msg)

def parity(monomial):
    value=0
    for i in monomial:value^=1<<i
    return value

def sign_symmetries(variables,rows,semantic):
    basis={}
    for row in rows:
        forms=[parity(m) for c,m in row['terms'] if c]
        require(forms,'zero row')
        for q in forms[1:]:
            z=q^forms[0]
            while z:
                k=z.bit_length()-1
                if k in basis:z^=basis[k]
                else:basis[k]=z;break
    n=len(variables)
    vectors=[]
    for f in range(n):
        if f in basis:continue
        z=1<<f
        for k in sorted(basis):
            if (basis[k]&z).bit_count()%2:z^=1<<k
        flips=[i for i in range(n) if z>>i&1]
        targets=[i for i in flips if i in semantic]
        require(len(targets)==1,'basis has more than one semantic coordinate')
        vectors.append({'normalized_variable':targets[0],'flip_variables':flips})
    require(len({x['normalized_variable'] for x in vectors})==len(vectors),'repeated semantic pivot')
    return vectors,len(basis)

def canonical(terms):
    out=defaultdict(int)
    for c,m in terms:out[tuple(sorted(m))]+=c
    return [[c,list(m)] for m,c in sorted(out.items()) if c]

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--source',type=Path,default=SOURCE)
    parser.add_argument('--optimization',type=Path,default=HERE/'preliminary.json')
    parser.add_argument('--output',type=Path,default=HERE/'candidate')
    args=parser.parse_args()
    raw=args.source.read_bytes();parent=json.loads(raw)
    nc=parent['metrics']['core_variables'];nr=parent['metrics']['core_rows']
    corevars=parent['variables'][:nc];corerows=parent['residuals'][:nr]
    semantic={i for i,v in enumerate(corevars) if v['kind'] in ('outer','witness')}
    optimization=json.loads(args.optimization.read_text())
    seeds=optimization['seeds'];steps=optimization['steps']
    symmetries,rank=sign_symmetries(corevars,corerows,semantic)
    require(set(optimization['symmetry_coordinates'])=={s['normalized_variable'] for s in symmetries},'normalization mismatch')
    variables=deepcopy(corevars);rows=deepcopy(corerows);guards=[]
    for i in seeds:
        abc=[]
        for letter in 'abc':
            abc.append(len(variables))
            variables.append({'kind':'guard_auxiliary','name':f'nat.{i}.{letter}'})
        a,b,c=abc
        rows.append({'label':f'nonnegative.{i}','terms':canonical([
            [1,[i]],[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]])})
        guards.append({'input':i,'auxiliaries':abc})
    expansion=defaultdict(int)
    for row in rows:
        require(all(len(m)<=2 for c,m in row['terms']),'nonquadratic row')
        for c,m in row['terms']:
            for d,n in row['terms']:expansion[tuple(sorted(m+n))]+=c*d
    poly=[[c,list(m)] for m,c in sorted(expansion.items()) if c]
    require({i for c,m in poly for i in m}==set(range(len(variables))),'unused final coordinate')
    metrics={'variables':len(variables),'quadratic_rows':len(rows),'exact_degree':max(len(m) for c,m in poly),
             'expanded_monomials':len(poly),'coefficient_height':max(abs(c) for c,m in poly),
             'core_variables':nc,'core_rows':nr,'semantic_coordinates':len(semantic),
             'guarded_coordinates':len(seeds),'sign_normalized_coordinates':len(symmetries),
             'inferred_semantic_coordinates':len(semantic)-len(seeds)-len(symmetries),
             'bound_derivation_steps':len(steps),'signed_quotients':sum(v['kind']=='signed_quotient' for v in corevars),
             'guard_auxiliaries':3*len(seeds),'sign_constraint_rank':rank,
             'variable_reduction_from_8619':8619-len(variables)}
    cert={'source_sha256':sha256(raw).hexdigest(),'core_variables':nc,'core_rows':nr,
          'guarded_coordinates':seeds,'sign_symmetries':symmetries,
          'bound_derivations':steps,'final_lower_bounds':optimization['bounds'],
          'certificate_kind':'exact sign automorphisms and ordered polynomial nonnegativity implications'}
    equation={'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers',
              'polynomial':'sum(square(row) for row in residuals)',
              'source_6628_sha256':sha256(raw).hexdigest(),'variables':variables,'residuals':rows,
              'natural_input_guards':guards,'metrics':metrics}
    out=args.output;out.mkdir(exist_ok=True)
    hashes={}
    for name,obj in [('equation.json',equation),('expanded_polynomial.json',{'domain':'unrestricted integers','variables':len(variables),'terms':poly}),('guard_certificate.json',cert)]:
        data=(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode();(out/name).write_bytes(data);hashes[name]=sha256(data).hexdigest()
    receipt={'status':'BUILT','metrics':metrics,'sha256':hashes}
    (out/'BUILD.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))

if __name__=='__main__':main()
