#!/usr/bin/env python3
"""Replay an explicit acyclic list of integral monic eliminations.

All pivots refer to the original 216-coordinate source. The emitted circuit
is the literal substituted polynomial, with no variable exponents or division.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import random
from pathlib import Path
from build import ROOT,Circuit,parse,serial,add,mul,sub,sq,scale,canonical,degree_witness,height_bound_bits

def compile_profile(profile):
    src=json.loads((ROOT/'inputs/source216.json').read_text())
    it=json.loads((ROOT/'inputs/interface216.json').read_text())
    actual_source_hash=hashlib.sha256((ROOT/'inputs/source216.json').read_bytes()).hexdigest()
    if actual_source_hash!=it['source_sha256']:raise ValueError('Source hash mismatch')
    if profile.get('source_sha256',actual_source_hash)!=actual_source_hash:raise ValueError('Profile source hash mismatch')
    rows=[parse(r['terms']) for r in src['residuals']]
    steps=profile['steps'];removed_rows=set();defs={};proof=[]
    forbidden=set(it['deleted_variables'])
    for step in steps:
        r,v=step['row'],step['variable']
        if r not in it['retained_rows'] or r in removed_rows or v in defs or v in forbidden:
            raise ValueError('Duplicate, protected or absent pivot')
        p=rows[r];eps=p.get((v,),0)
        if eps not in (-1,1) or any(v in m and m!=(v,) for m in p):
            raise ValueError('Pivot not a unit-slope monic original row')
        f=scale(-eps,{m:c for m,c in p.items() if m!=(v,)})
        if any(i in forbidden for m in f for i in m):raise ValueError('Private dependency')
        defs[v]=f;removed_rows.add(r)
        proof.append({'row':r,'variable':v,'unit_coefficient':eps,'definition':serial(f)})
    partition=profile.get('partition',[[0,1,2,3,4]])
    if sorted(i for p in partition for i in p)!=list(range(5)):raise ValueError('Bad partition')
    free=[i for i in it['retained_variables'] if i not in defs]
    mp={v:i for i,v in enumerate(free)};c=Circuit();cache={};visiting=set();resolution_order=[]
    def poly(p):
        parts=[]
        for m,a in sorted(p.items()):
            t=c.product([resolve(v) for v in m])
            if a!=1:t=c.times(c.const(a),t)
            parts.append(t)
        return c.sum(parts)
    def resolve(v):
        if v in cache:return cache[v]
        if v in visiting:raise ValueError('Cyclic definitions')
        visiting.add(v)
        if v in defs:
            z=poly(defs[v]);resolution_order.append(v)
        elif v in mp:z=c.var(mp[v])
        else:raise ValueError('Undefined source coordinate')
        visiting.remove(v);cache[v]=z;return z
    # Resolve all deleted definitions, even if a later simplification makes
    # one output unused. This verifies the complete inverse lift.
    for v in defs:resolve(v)
    kept=[r for r in it['retained_rows'] if r not in removed_rows]
    outputs=[poly(rows[r]) for r in kept]
    req={r['request']:r for r in it['requests']}
    ns=[];ts=[];es=[]
    for b in it['blocks']:
        n=poly(parse(b['base']));ns.append(n);ts.append(poly(parse(b['T'])))
        hr=[];sr=[]
        for j in b['requests']:
            r=req[j];yy=poly(parse(r['Y']));mm=poly(parse(r['m']))
            xx=poly(parse(r['X']));dd=poly(parse(r['D']))
            hr.append(c.times(yy,c.minus(mm,xx)))
            sr.append(c.minus(c.square(c.minus(mm,dd)),c.square(yy)))
        es.append(c.minus(c.sum(sr),c.product([c.const(2),n,c.sum(hr)])))
    variables=[{**src['variables'][i],'source_index':i} for i in free]
    for i,ids in enumerate(partition):
        zi=len(variables);variables.append({'name':f'mixed_pool.z{i}','kind':'unrestricted integer'})
        summands=[c.product([es[j]]+[ts[h] for h in ids if h!=j]) for j in ids]
        outputs.append(c.minus(c.sum(summands),c.product([c.var(zi)]+[ts[h] for h in ids])))
    target=c.sum([c.square(x) for x in outputs])
    nodes,newout=c.compact(outputs+[target])
    circuit={'schema':'integer-polynomial-circuit-v1','domain':'unrestricted integers',
             'variables':variables,'nodes':nodes,'residual_outputs':newout[:-1],'output':newout[-1],
             'leaf_convention':'var index is the zero-based variables array; const is an integer; every binary operand is an earlier node'}
    # Exact integer evaluation of a highest homogeneous form is a proof of
    # the degree, not a probabilistic claim of polynomial identity.
    witnesses=[]
    for seed in range(20):
        rng=random.Random(seed);point={i:rng.randrange(1,8) for i in range(len(variables))}
        w=degree_witness(circuit,point)
        if w['leading_value']:
            witnesses.append(w);break
    if not witnesses:raise ValueError('No nonzero top form witness')
    degree=witnesses[0]['upper_degree']
    expected=profile.get('degree_bound',degree)
    if degree>expected:raise ValueError(f'Degree {degree} exceeds profile {expected}')
    used={n[1] for n in nodes if n[0]=='var'}
    if used!=set(range(len(variables))):raise ValueError('Unused input')
    metrics={'variables':len(variables),'residuals':len(outputs),'exact_total_degree':degree,
             'deleted_monic_coordinates':len(defs),'retained_source_residuals':len(kept),
             'new_pool_residuals':len(partition),
             'binary_operations':sum(n[0] in ('+','-','*') for n in nodes),
             'maximum_literal_integer':max(abs(n[1]) for n in nodes if n[0]=='const'),
             'expanded_support':'not computed','expanded_coefficient_height':'not computed',
             'coefficient_height_strictly_less_than_2_power':height_bound_bits(circuit),
             'degree_certificate':witnesses[0]}
    certificate={'schema':'monic-projection-v1','source_sha256':it['source_sha256'],
                 'partition':partition,'steps':proof,'free_source_coordinates':free,
                 'retained_source_rows':kept,'resolution_order':resolution_order,
                 'pool_deleted_coordinates':it['deleted_variables'],'pool_deleted_rows':it['deleted_rows'],
                 'circuit_sha256':hashlib.sha256(canonical(circuit)).hexdigest(),
                 'inverse':'Resolve the acyclic monic definitions; use the mixed-base theorem to restore the ten private power coordinates.'}
    return circuit,metrics,certificate

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('profile',type=Path)
    ap.add_argument('--output',type=Path,default=ROOT/'equations');args=ap.parse_args()
    profile=json.loads(args.profile.read_text());profile=profile.get('best',profile)
    circ,met,cert=compile_profile(profile)
    name=f"integer{met['variables']}_degree{met['exact_total_degree']}"
    dest=args.output/name;dest.mkdir(parents=True,exist_ok=True)
    for fn,obj in [('circuit.json',circ),('METRICS.json',met),('projection.json',cert),('profile.json',profile)]:
        (dest/fn).write_bytes(canonical(obj))
    print(json.dumps({'endpoint':name,**{k:v for k,v in met.items() if k!='degree_certificate'}},sort_keys=True,indent=2))

if __name__=='__main__':main()
