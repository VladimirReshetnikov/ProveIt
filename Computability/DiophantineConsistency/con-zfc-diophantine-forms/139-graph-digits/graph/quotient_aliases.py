#!/usr/bin/env python3
"""Exact support-aware alias quotients of a graph energy.

Every accepted identification is between aliases of one logical coordinate.
Acceptance uses all collected energy coefficients, not point evaluations.
The graph energy identity and rebuilt alias cycles are independently auditable.
"""
import argparse
from collections import Counter, defaultdict
from copy import deepcopy
import json
from pathlib import Path
import random
import time


def dump(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, sort_keys=True, separators=(",", ":"))+"\n")


def energy(certificate):
    ans = Counter()
    incident = [[] for _ in certificate['vertices']]
    for edge in certificate['edges']:
        c, m = edge['coefficient'], tuple(sorted(edge['monomial']))
        ans[tuple(sorted(m+m))] += c*c
        incident[edge['tail']].append((c,m))
        incident[edge['head']].append((-c,m))
    for row in incident:
        for i,(c,m) in enumerate(row):
            for d,n in row[i+1:]:
                ans[tuple(sorted(m+n))] += c*d
    return {m:c for m,c in ans.items() if c}


def quotient(artifact, cert, seed=0, strategy='support', rounds=2):
    original_variables=artifact['variables']
    excluded={i for i,v in enumerate(original_variables) if v['kind'] in ('equality_dummy','unit_dummy')}
    groups=[]
    for cy in cert['equality_cycles']:
        groups.append([v for v in cy['aliases'] if v not in excluded])
    groups.append([v for v in cert['unit_path'] if v not in excluded])
    parent=list(range(len(original_variables)))
    def root(v):
        while parent[v]!=v:
            parent[v]=parent[parent[v]];v=parent[v]
        return v
    pol=energy(cert)
    if any(abs(c)!=1 for c in pol.values()):
        raise ValueError('Starting energy is not height one')
    occurs=defaultdict(set)
    for m in pol:
        for v in set(m):occurs[v].add(m)
    attempts=0;accepted=[]
    def merge(a,b):
        nonlocal attempts
        attempts+=1
        # Substitute a -> b and collect all affected coefficients exactly.
        delta=Counter()
        affected=list(occurs[a])
        for m in affected:
            c=pol[m]
            n=tuple(sorted(b if x==a else x for x in m))
            delta[m]-=c;delta[n]+=c
        if any(abs(pol.get(m,0)+c)>1 for m,c in delta.items()):return False
        for m,c in delta.items():
            if not c:continue
            old=pol.get(m,0);new=old+c
            if old:
                for v in set(m):occurs[v].discard(m)
            if new:
                pol[m]=new
                for v in set(m):occurs[v].add(m)
            else:pol.pop(m,None)
        parent[a]=b
        accepted.append([a,b])
        return True
    rng=random.Random(seed)
    for sweep in range(rounds):
        before=len(accepted)
        order=list(range(len(groups)))
        if strategy=='random':rng.shuffle(order)
        elif strategy=='support':order.sort(key=lambda i:-sum(len(occurs[root(v)]) for v in groups[i]))
        for g in order:
            vs=sorted(set(root(v) for v in groups[g]))
            if strategy=='random':rng.shuffle(vs)
            else:vs.sort(key=lambda v:(-len(occurs[v]),v))
            # Try every unordered pair of live representatives.
            for i in range(len(vs)):
                if root(vs[i])!=vs[i]:continue
                for j in range(i+1,len(vs)):
                    if root(vs[j])!=vs[j]:continue
                    # Preserve vs[i]; substitute the other representative.
                    merge(vs[j],vs[i])
        if len(accepted)==before:break

    # Rebuild a fresh coordinate system, graph labels and equality energies.
    keep=[i for i in range(len(original_variables)) if i not in excluded and root(i)==i]
    rename={old:new for new,old in enumerate(keep)}
    mapping={i:rename[root(i)] for i in range(len(original_variables)) if i not in excluded}
    variables=[]
    for old in keep:
        v=deepcopy(original_variables[old])
        if v['kind']!='flow':
            v={'kind':'logical_alias','normalized_variable':v.get('normalized_variable'),
               'origin_aliases':[i for i in range(len(original_variables)) if i not in excluded and root(i)==old]}
        variables.append(v)
    newcert=deepcopy(cert)
    for e in newcert['edges']:e['monomial']=[mapping[v] for v in e['monomial']]
    for p in newcert.get('products',[]):p['factors']=[mapping[v] for v in p['factors']]
    final=Counter({tuple(sorted(rename[x] for x in m)):c for m,c in pol.items()})
    cycles=[]
    for oldcy in cert['equality_cycles']:
        av=sorted(set(mapping[v] for v in oldcy['aliases'] if v not in excluded))
        if len(av)==2:
            av.append(len(variables));variables.append({'kind':'equality_dummy','normalized_variable':oldcy['normalized_variable']})
        if len(av)>1:
            for v in av:final[(v,v)]+=1
            for a,b in zip(av,av[1:]+av[:1]):final[tuple(sorted((a,b)))]-=1
        cycles.append({'normalized_variable':oldcy['normalized_variable'],'aliases':av})
    units=sorted(set(mapping[v] for v in cert['unit_path'] if v not in excluded))
    while len(units)<2:
        units.append(len(variables));variables.append({'kind':'unit_dummy'})
    final[()]+=1
    for v in units:final[(v,v)]+=1
    for a,b in zip(units,units[1:]):final[tuple(sorted((a,b)))]-=1
    final[(units[0],)]-=1;final[(units[-1],)]-=1
    final={m:c for m,c in final.items() if c}
    if any(abs(c)!=1 for c in final.values()):raise ValueError('Non-unit coefficient after alias energy')
    used={v for m in final for v in m}
    if used!=set(range(len(variables))):raise ValueError('Unused coordinate')
    newcert['equality_cycles']=cycles;newcert['unit_path']=units
    newcert['alias_quotient']={'origin_variables':len(original_variables),'identifications':accepted,
        'mapping':[[i,mapping[i]] for i in sorted(mapping)],'strategy':strategy,'seed':seed,'attempts':attempts}
    metrics={'variables':len(variables),'degree':max(map(len,final)),'monomials':len(final),
        'coefficient_height':1,'constant':final.get((),0),
        'individual_degree':max(max(Counter(m).values(),default=0) for m in final),
        'source_variables':len(cert['normalization']['variables'])-cert['normalization']['constant_count']-cert['normalization']['scale_count'],
        'normalized_variables':len(cert['normalization']['variables']),
        'normalized_rows':len(cert['normalization']['rows']),
        'identifications':len(accepted),'energy_monomials':len(pol),
        'flow_variables':sum(v['kind']=='flow' for v in variables),
        'equality_dummies':sum(v['kind']=='equality_dummy' for v in variables),
        'unit_coordinates':len(units),'positive_coefficients':sum(c>0 for c in final.values()),
        'negative_coefficients':sum(c<0 for c in final.values()),
        'hubs':len(cert['hub_vertices'])}
    out={'schema':'support-aware-graph-quartic-v1','domain':'unrestricted integers',
        'variables':variables,'terms':[[final[m],list(m)] for m in sorted(final,key=lambda m:(len(m),m))],
        'metrics':metrics}
    return out,newcert


def main():
    pa=argparse.ArgumentParser();pa.add_argument('--input',type=Path,required=True);pa.add_argument('--output',type=Path,required=True)
    pa.add_argument('--seed',type=int,default=0);pa.add_argument('--strategy',choices=['support','random'],default='support');pa.add_argument('--rounds',type=int,default=2)
    args=pa.parse_args();start=time.time()
    p,c=quotient(json.loads((args.input/'polynomial.json').read_text()),json.loads((args.input/'certificate.json').read_text()),args.seed,args.strategy,args.rounds)
    dump(args.output/'polynomial.json',p);dump(args.output/'certificate.json',c);dump(args.output/'metrics.json',p['metrics'])
    print(json.dumps({'metrics':p['metrics'],'seconds':round(time.time()-start,2)},sort_keys=True),flush=True)


if __name__=='__main__':main()
