#!/usr/bin/env python3
"""Independent verifier for exact local alias contraction.

Imports no construction or optimization code.  It verifies the old graph with
its separately supplied original verifier, validates the whole substitution
map and new equality guards, and reconstructs twice the new polynomial by
literal sums of quadratic squares.  All checks survive python -O.
"""
import argparse
from collections import Counter, defaultdict
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent

def need(condition,message):
    if not condition: raise ValueError(message)

def add(target,mon,c):
    mon=tuple(sorted(mon)); total=target.get(mon,0)+c
    if total: target[mon]=total
    else: target.pop(mon,None)

def square_add(target,terms):
    collected={}
    for c,mon in terms: add(collected,mon,c)
    for a,c in collected.items():
        for b,d in collected.items(): add(target,a+b,c*d)

def readpoly(terms,n):
    result={}
    for c,m in terms:
        need(type(c)is int and c!=0,'Invalid coefficient')
        need(all(type(x)is int and 0<=x<n for x in m),'Invalid variable')
        need(m==sorted(m),'Noncanonical monomial')
        k=tuple(m); need(k not in result,'Duplicate polynomial monomial')
        result[k]=c
    return result

def check(parent,old,new,cert):
    mapping=cert['parent_to_child']; n=len(new['variables'])
    need(new['domain']=='unrestricted integers','Domain mismatch')
    need(new['schema']=='unit-quartic-incidence-local-v1','New schema mismatch')
    need(cert['schema']=='incidence-local-alias-contraction-v1','Certificate schema')
    need(len(mapping)==len(parent['variables']),'Map dimension')
    need(all(x is None or type(x)is int and 0<=x<n for x in mapping),'Map coordinate')
    old_classes={}
    for r in old['equality_cycles']:
        for x in r['aliases']:
            need(x not in old_classes,'Parent class overlap')
            old_classes[x]=r['normalized_variable']
    old_units=set(old['unit_path'])
    # The optional human-readable merger sequence must reproduce exactly
    # the same partition as the authoritative map.
    replay=list(range(len(mapping)))
    for step in cert['merge_log']:
        need(isinstance(step,list) and len(step)==2,'Malformed merger step')
        a,b=step
        need(type(a)is int and type(b)is int and 0<=a<len(mapping) and 0<=b<len(mapping),'Merger coordinate')
        need(a!=b and replay[a]==a and replay[b]==b,'Merger representatives')
        same=(a in old_classes and b in old_classes and old_classes[a]==old_classes[b]) or (a in old_units and b in old_units)
        need(same,'Merger crosses logical classes')
        replay=[b if x==a else x for x in replay]
    representative_targets={}; reverse_targets={}
    for i,t in enumerate(mapping):
        if t is None: continue
        r=replay[i]
        need(r not in representative_targets or representative_targets[r]==t,'Merger log/map mismatch')
        need(t not in reverse_targets or reverse_targets[t]==r,'Unrecorded merger')
        representative_targets[r]=t;reverse_targets[t]=r
    mapped_logical=defaultdict(set); mapped_units=set(); mapped_flows={}
    for i,v in enumerate(parent['variables']):
        k=v['kind']; target=mapping[i]
        if k in ('equality_dummy','unit_dummy'):
            need(target is None,'Old dummy must be reconstructed, not mapped')
            continue
        need(target is not None,'Non-dummy parent coordinate lost')
        desc=new['variables'][target]
        if i in old_classes:
            logical=old_classes[i]
            need(desc['kind']=='alias' and desc['normalized_variable']==logical,'Logical alias changed')
            mapped_logical[logical].add(target)
        elif i in old_units:
            need(desc['kind']=='unit','Unit alias changed')
            mapped_units.add(target)
        else:
            need(k=='flow' and desc=={'kind':'flow','parent_variable':i},'Flow changed')
            need(target not in mapped_flows,'Merged independent flows')
            mapped_flows[target]=i
    need(set(mapped_logical)=={r['normalized_variable'] for r in old['equality_cycles']},'Lost logical class')
    need(set(mapped_flows)=={i for i,v in enumerate(new['variables']) if v['kind']=='flow'},'Extra flow coordinate')
    # Metadata must state precisely the original occurrences represented.
    inverse=defaultdict(list)
    for i,t in enumerate(mapping):
        if t is not None: inverse[t].append(i)
    for i,v in enumerate(new['variables']):
        if v['kind'] in ('alias','unit'):
            need(v['parent_aliases']==inverse[i], 'Alias inverse metadata')
    twice={}; divergences=[[] for _ in old['vertices']]
    for e in old['edges']:
        mon=[mapping[x] for x in e['monomial']]
        need(None not in mon,'Edge uses discarded dummy')
        divergences[e['tail']].append((e['coefficient'],mon))
        divergences[e['head']].append((-e['coefficient'],mon))
    for row in divergences: square_add(twice,row)
    seen_classes=set(); constrained=set(mapped_flows); quartics=0
    for row in cert['equality_cycles']:
        logical=row['normalized_variable']; aliases=row['aliases']; kind=row['kind']
        need(logical not in seen_classes,'Repeated new logical class')
        seen_classes.add(logical)
        need(len(aliases)==len(set(aliases)) and aliases,'Bad alias list')
        need(all(type(x)is int and 0<=x<n for x in aliases),'Alias coordinate')
        need(not constrained.intersection(aliases),'New class overlap')
        constrained.update(aliases)
        substantive={x for x in aliases if new['variables'][x]['kind']=='alias'}
        dummies=[x for x in aliases if new['variables'][x]['kind']=='equality_dummy']
        need(substantive==mapped_logical[logical],'Class does not cover exactly mapped aliases')
        need(len(substantive)+len(dummies)==len(aliases),'Foreign class coordinate')
        need(all(new['variables'][x]=={'kind':'equality_dummy','normalized_variable':logical} for x in dummies),'Wrong equality dummy')
        if kind=='singleton':
            need(len(aliases)==1 and not dummies,'Bad singleton')
        elif kind=='cycle':
            need(len(aliases)>=3,'Cycle has fewer than three vertices')
            need(len(dummies)==(1 if len(substantive)==2 else 0),'Unexpected cycle dummy')
            for a,b in zip(aliases,aliases[1:]+aliases[:1]):
                square_add(twice,[(1,[a]),(-1,[b])])
        elif kind=='quartic_pair':
            need(len(aliases)==2 and not dummies,'Bad quartic pair')
            a,b=aliases; quartics+=1
            # 2(a-b)^2(a^2+ab+b^2), independently as three squares.
            square_add(twice,[(1,[a,a]),(-1,[b,b])])
            square_add(twice,[(1,[a,a]),(-1,[a,b])])
            square_add(twice,[(1,[a,b]),(-1,[b,b])])
        else: raise ValueError('Unknown equality guard')
    need(seen_classes==set(mapped_logical),'New class inventory')
    units=cert['unit_path']
    need(len(units)>=2 and len(units)==len(set(units)),'Unit path size')
    need(all(type(x)is int and 0<=x<n for x in units),'Unit coordinate')
    need(not constrained.intersection(units),'Unit namespace collision')
    constrained.update(units)
    need({x for x in units if new['variables'][x]['kind']=='unit'}==mapped_units,'Unit map coverage')
    need(all(new['variables'][x]['kind'] in ('unit','unit_dummy') for x in units),'Foreign unit coordinate')
    need(constrained==set(range(n)),'Unconstrained or extra new variable')
    square_add(twice,[(1,[units[0]]),(-1,[])])
    square_add(twice,[(1,[units[-1]]),(-1,[])])
    for a,b in zip(units,units[1:]): square_add(twice,[(1,[a]),(-1,[b])])
    need(all(c%2==0 for c in twice.values()),'Half-energy is not integral')
    expected={m:c//2 for m,c in twice.items()}
    actual=readpoly(new['terms'],n)
    need(actual==expected,'Complete polynomial coefficient mismatch')
    need(set(actual.values())<=set((-1,1)),'Coefficient height exceeds one')
    need(actual.get(())==1,'Constant differs from one')
    need(set(x for m in actual for x in m)==set(range(n)),'Unused output variable')
    metrics={'variables':n,'degree':max(map(len,actual)),
      'coefficient_height':max(map(abs,actual.values())), 'monomials':len(actual),
      'constant':actual.get((),0), 'individual_degree':max(max(Counter(m).values(),default=0) for m in actual),
      'positive_coefficients':sum(c>0 for c in actual.values()),'negative_coefficients':sum(c<0 for c in actual.values()),
      'flow_variables':len(mapped_flows),'quartic_pair_guards':quartics,
      'equality_dummies':sum(v['kind']=='equality_dummy' for v in new['variables']),
      'unit_coordinates':len(units),'parent_variables':len(parent['variables'])}
    need(metrics==new['metrics'],'Metric mismatch')
    need(metrics['degree']==4,'Expected total degree four')
    return metrics

def main():
    p=argparse.ArgumentParser();p.add_argument('--parent',type=Path,default=HERE/'parents/matched1252')
    p.add_argument('--artifact',type=Path,default=HERE/'matched1252')
    p.add_argument('--source',type=Path,default=HERE/'sources/source442.json')
    p.add_argument('--receipt',type=Path);p.add_argument('--mutations',action='store_true')
    args=p.parse_args()
    parent=json.loads((args.parent/'polynomial.json').read_text())
    old=json.loads((args.parent/'certificate.json').read_text())
    new=json.loads((args.artifact/'polynomial.json').read_text())
    cert=json.loads((args.artifact/'certificate.json').read_text())
    loader=importlib.util.spec_from_file_location('original_independent_graph_verifier',HERE/'inherited/verify_graph.py')
    inherited=importlib.util.module_from_spec(loader);loader.loader.exec_module(inherited)
    source_bytes=args.source.read_bytes()
    inherited.verify(json.loads(source_bytes),parent,old,hashlib.sha256(source_bytes).hexdigest())
    metrics=check(parent,old,new,cert)
    rejected=[]
    if args.mutations:
        cases=[]
        a=deepcopy(new);a['terms'][0][0]=-a['terms'][0][0];cases.append(('constant sign',a,cert))
        a=deepcopy(cert);a['equality_cycles']=a['equality_cycles'][1:];cases.append(('missing equality class',new,a))
        a=deepcopy(cert);a['unit_path']=a['unit_path'][:-1];cases.append(('missing unit coordinate',new,a))
        a=deepcopy(cert)
        choices=[i for i,x in enumerate(a['parent_to_child']) if x is not None and i in {v for r in old['equality_cycles'] for v in r['aliases']}]
        first=choices[0]; target=a['parent_to_child'][first]
        second=next(i for i in choices if new['variables'][a['parent_to_child'][i]].get('normalized_variable')!=new['variables'][target].get('normalized_variable'))
        a['parent_to_child'][first]=a['parent_to_child'][second];cases.append(('cross-class alias merger',new,a))
        for label,aa,cc in cases:
            try: check(parent,old,aa,cc)
            except (ValueError,KeyError,TypeError,IndexError): rejected.append(label)
            else: raise ValueError('Corruption accepted: '+label)
    receipt={'status':'pass','metrics':metrics,'mutations_rejected':rejected,
      'source_sha256':hashlib.sha256(source_bytes).hexdigest(),
      'polynomial_sha256':hashlib.sha256((args.artifact/'polynomial.json').read_bytes()).hexdigest(),
      'checks':['inherited source normalization and parent polynomial','complete logical alias map',
      'unchanged independent flow variables','complete regenerated equality guards and unit path',
      'full independent expansion as half a sum of squares','all collected coefficients and metrics'],
      'scope':'Exact finite algebraic certificate; unbounded zero-set proof and inherited C222/ZF/ZFC calibration remain ordinary mathematical dependencies.'}
    text=json.dumps(receipt,sort_keys=True,indent=2)+'\n'
    if args.receipt: args.receipt.write_text(text)
    print(text,end='')

if __name__=='__main__': main()
