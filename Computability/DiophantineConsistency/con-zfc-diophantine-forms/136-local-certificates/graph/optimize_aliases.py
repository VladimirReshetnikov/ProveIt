#!/usr/bin/env python3
"""Exact incidence-local contraction of equal-value graph aliases.

Only the old logical alias classes may merge.  A merge is admitted exactly
when all coefficients of the collected graph energy still belong to {-1,0,1}.
Equality cycles are rebuilt after contraction.  No numerical sampling occurs.
"""
import argparse
from collections import defaultdict, Counter
from copy import deepcopy
import json
from pathlib import Path
import random
import time

HERE=Path(__file__).resolve().parent

def add(poly, mon, c):
    mon=tuple(sorted(mon)); value=poly.get(mon,0)+c
    if value: poly[mon]=value
    else: poly.pop(mon,None)

def energy(cert):
    poly={}; incident=[[] for _ in cert['vertices']]
    for e in cert['edges']:
        c,mon=e['coefficient'],e['monomial']
        add(poly,mon+mon,c*c)
        incident[e['tail']].append((c,mon))
        incident[e['head']].append((-c,mon))
    for terms in incident:
        for i,(c,a) in enumerate(terms):
            for d,b in terms[i+1:]: add(poly,a+b,c*d)
    return poly

class State:
    def __init__(self,cert,artifact):
        self.poly=energy(cert)
        self.index=defaultdict(set)
        for mon in self.poly:
            for x in set(mon): self.index[x].add(mon)
        self.groups=[]
        for row in cert['equality_cycles']:
            self.groups.append([x for x in row['aliases']
                if artifact['variables'][x]['kind']!='equality_dummy'])
        self.groups.append([x for x in cert['unit_path']
            if artifact['variables'][x]['kind']!='unit_dummy'])
        self.map=list(range(len(artifact['variables'])))
        self.log=[]
    def merge(self,a,b):
        if a==b: return False
        affected=list(self.index[a]); delta=Counter()
        for mon in affected:
            c=self.poly[mon]
            delta[mon]-=c
            target=tuple(sorted(b if x==a else x for x in mon))
            delta[target]+=c
        if any(abs(self.poly.get(mon,0)+c)>1 for mon,c in delta.items()):
            return False
        for mon,c in delta.items():
            if not c: continue
            before=self.poly.get(mon,0); after=before+c
            if before:
                for x in set(mon): self.index[x].discard(mon)
            if after:
                self.poly[mon]=after
                for x in set(mon): self.index[x].add(mon)
            else: self.poly.pop(mon,None)
        self.map=[b if x==a else x for x in self.map]
        self.log.append([a,b])
        return True

def optimize(cert,artifact,seed=0,rounds=8):
    state=State(cert,artifact); rng=random.Random(seed)
    attempts=0
    for round_no in range(rounds):
        accepted=0
        order=list(range(len(state.groups)))
        if seed: rng.shuffle(order)
        for gid in order:
            group=state.groups[gid]
            while True:
                pairs=[(a,b) for i,a in enumerate(group) for b in group[i+1:]]
                if seed: rng.shuffle(pairs)
                else: pairs.sort(key=lambda ab:(len(state.index[ab[0]])+len(state.index[ab[1]]),ab))
                changed=False
                for a,b in pairs:
                    attempts+=1
                    if len(state.index[a])>len(state.index[b]): a,b=b,a
                    if state.merge(a,b):
                        group.remove(a); accepted+=1; changed=True; break
                if not changed: break
        if not accepted: break
    return state,{'attempts':attempts,'accepted_merges':len(state.log),'rounds':round_no+1,'seed':seed}

def emit(state,cert,artifact,quartic_guards=False):
    active=sorted({x for mon in state.poly for x in mon})
    # All alias class representatives and every flow must be retained.
    required=set(x for g in state.groups for x in g)
    required.update(i for i,v in enumerate(artifact['variables']) if v['kind']=='flow')
    active=sorted(set(active)|required)
    index={old:new for new,old in enumerate(active)}
    variables=[]
    old_class={x:row['normalized_variable'] for row in cert['equality_cycles'] for x in row['aliases']}
    units=set(cert['unit_path'])
    for old in active:
        aliases=[i for i,x in enumerate(state.map) if x==old and artifact['variables'][i]['kind'] not in ('equality_dummy','unit_dummy')]
        if old in old_class:
            variables.append({'kind':'alias','normalized_variable':old_class[old], 'parent_aliases':aliases})
        elif old in units: variables.append({'kind':'unit','parent_aliases':aliases})
        else: variables.append({'kind':'flow','parent_variable':old})
    p={tuple(index[x] for x in mon):c for mon,c in state.poly.items()}
    cycles=[]
    for g,row in zip(state.groups[:-1],cert['equality_cycles']):
        aliases=sorted(index[x] for x in g)
        if len(aliases)==2 and quartic_guards:
            a,b=aliases
            guard={(a,a,a,a):1,(b,b,b,b):1,(a,a,a,b):-1,(a,b,b,b):-1}
            if all(abs(p.get(m,0)+c)<=1 for m,c in guard.items()):
                for m,c in guard.items(): add(p,m,c)
                cycles.append({'kind':'quartic_pair','normalized_variable':row['normalized_variable'],'aliases':aliases})
                continue
        if len(aliases)==2:
            aliases.append(len(variables))
            variables.append({'kind':'equality_dummy','normalized_variable':row['normalized_variable']})
        cycles.append({'kind':'cycle' if len(aliases)>1 else 'singleton','normalized_variable':row['normalized_variable'],'aliases':aliases})
        if len(aliases)>1:
            for x in aliases: add(p,[x,x],1)
            for a,b in zip(aliases,aliases[1:]+aliases[:1]): add(p,[a,b],-1)
    units=sorted(index[x] for x in state.groups[-1])
    while len(units)<2:
        units.append(len(variables)); variables.append({'kind':'unit_dummy'})
    add(p,[],1)
    for x in units: add(p,[x,x],1)
    for a,b in zip(units,units[1:]): add(p,[a,b],-1)
    add(p,[units[0]],-1); add(p,[units[-1]],-1)
    if any(abs(c)>1 for c in p.values()): raise ValueError('Final coefficient collision')
    metrics={'variables':len(variables),'degree':max(map(len,p)),
      'coefficient_height':max(map(abs,p.values())), 'monomials':len(p),
      'constant':p.get((),0), 'individual_degree':max(max(Counter(m).values(),default=0) for m in p),
      'positive_coefficients':sum(c>0 for c in p.values()),'negative_coefficients':sum(c<0 for c in p.values()),
      'flow_variables':sum(v['kind']=='flow' for v in variables),
      'quartic_pair_guards':sum(r['kind']=='quartic_pair' for r in cycles),
      'equality_dummies':sum(v['kind']=='equality_dummy' for v in variables),
      'unit_coordinates':len(units),'parent_variables':len(artifact['variables'])}
    renaming=[index[state.map[x]] if state.map[x] in index else None for x in range(len(state.map))]
    proof={'schema':'incidence-local-alias-contraction-v1','parent_to_child':renaming,
       'equality_cycles':cycles,'unit_path':units,'merge_log':state.log}
    result={'schema':'unit-quartic-incidence-local-v1','domain':'unrestricted integers',
       'variables':variables,'terms':[[p[m],list(m)] for m in sorted(p,key=lambda a:(len(a),a))],
       'metrics':metrics}
    return result,proof

def write(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n')

def main():
    p=argparse.ArgumentParser(); p.add_argument('--seed',type=int,default=0)
    p.add_argument('--out',type=Path,default=HERE/'optimized')
    p.add_argument('--input',type=Path,default=HERE/'parents/matched1252')
    p.add_argument('--quartic-guards',action='store_true')
    args=p.parse_args()
    cert=json.loads((args.input/'certificate.json').read_text())
    art=json.loads((args.input/'polynomial.json').read_text())
    start=time.time(); state,summary=optimize(cert,art,args.seed)
    result,proof=emit(state,cert,art,args.quartic_guards)
    write(args.out/'polynomial.json',result); write(args.out/'certificate.json',proof)
    write(args.out/'metrics.json',result['metrics'])
    summary.update(result['metrics']); summary['seconds']=time.time()-start
    write(args.out/'search.json',summary); print(json.dumps(summary,indent=2))

if __name__=='__main__': main()
