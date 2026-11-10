#!/usr/bin/env python3
"""Bounded two-target shared-intermediate and direct-alias screen."""
import gzip
import hashlib
import json
from pathlib import Path
import random
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
control_kind=sys.argv[1:] or []
if control_kind not in ([],['--control'],['--alias-control']):
    raise SystemExit('usage: screen.py [--control|--alias-control]')
control_mode=bool(control_kind)
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
SOURCE=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
PIN='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
raw=SOURCE.read_bytes()
if hashlib.sha256(raw).hexdigest()!=PIN:raise RuntimeError('source hash mismatch')
g=json.loads(raw);rows=g['source'];output=g['output'];ports={}
for name,m in g['coefficient_binding']['ports'].items():
    packed=(SOURCE.parent/'coefficients'/m['file']).read_bytes()
    if hashlib.sha256(packed).hexdigest()!=m['gzip_sha256']:raise RuntimeError('gzip hash mismatch')
    data=gzip.decompress(packed)
    if hashlib.sha256(data).hexdigest()!=m['raw_sha256']:raise RuntimeError('raw hash mismatch')
    ports[name]=int.from_bytes(data,'big')
if control_mode:
    test_rows=([['a','+','x','y'],['b','+','x','y'],['c','+','a','z'],
                ['d','+','b','z'],['out','*','c','d']] if control_kind==['--alias-control'] else
               [['a','+','x','y'],['b','-','x','y'],['c','+','a','z'],
                ['d','+','b','z'],['out','*','c','d']])
    g={'witnesses':['x','y','z'],'fixed_numerals':[],
       'source':test_rows,'output':'out'}
    rows=g['source'];output=g['output'];ports={}
P=(1000000007,1000000009,998244353);SAMPLES=3;SEED=0x2C65
for p in P:
    if not all(p%d for d in range(2,int(p**0.5)+1)):raise RuntimeError('nonprime modulus')
mods=[p for p in P for _ in range(SAMPLES)];rng=random.Random(SEED)
values={x:tuple(rng.randrange(1,p) for p in mods) for x in g['witnesses']}
values.update({x:tuple(n%p for p in mods) for x,n in ports.items()})
values.update({x:(x,)*len(mods) for x in range(5)})
availability={x:0 for x in values};all_leaves=list(values)
def calc(op,a,b):
    return tuple((x+y if op=='+' else x-y if op=='-' else x*y)%p for x,y,p in zip(a,b,mods))
for index,(name,op,a,b) in enumerate(rows):
    if name in values or a not in values or b not in values:raise RuntimeError('invalid graph order')
    values[name]=calc(op,values[a],values[b]);availability[name]=index+1
    if any(v==0 for v in values[name]):raise RuntimeError(f'zero target sample: {name}')
for name in all_leaves:
    if name!=0 and any(v==0 for v in values[name]):raise RuntimeError(f'zero leaf sample: {name}')
names=all_leaves+[r[0] for r in rows]

def live(graph,out):
    edges={r[0]:r[2:] for r in graph};seen=set();todo=[out]
    while todo:
        x=todo.pop()
        if x in edges and x not in seen:seen.add(x);todo.extend(edges[x])
    return len(seen)
original=5 if control_mode else 65
if len(rows)!=original or live(rows,output)!=original:raise RuntimeError('unexpected graph')

# For each target, infer a shared value h from h+x, h-x, x-h, h*x.
# Every nonzero sample is invertible in its prime field; literal zero is
# omitted from division but remains available for the other three forms.
requirements={};counts={'target_queries':0,'shared_gate_forms':0,'matching_signatures':0,
                        'target_pairs':0,'tested_replacements':0,'constant_leaf_signatures':0}
for i,(target,_,_,_) in enumerate(rows):
    t=values[target]
    requirements.setdefault(t,[]).append((i,target,'alias',None));counts['target_queries']+=1
    for x in names:
        if availability[x]>i:continue
        v=values[x]
        opts=[('+',tuple((a-b)%p for a,b,p in zip(t,v,mods))),
              ('-',tuple((a+b)%p for a,b,p in zip(t,v,mods))),
              ('r-',tuple((b-a)%p for a,b,p in zip(t,v,mods)))]
        if x!=0:
            opts.append(('*',tuple(a*pow(b,-1,p)%p for a,b,p in zip(t,v,mods))))
        for kind,sig in opts:
            requirements.setdefault(sig,[]).append((i,target,kind,x));counts['target_queries']+=1

# Materialize only shared-gate signatures that at least two distinct targets
# request. Commutative +/* pairs use one ordering; subtraction uses both.
needed={s for s,items in requirements.items() if len({v[0] for v in items})>=2}
gate_matches={}
for a in names:
    if values[a] in needed:
        gate_matches.setdefault(values[a],[]).append((availability[a],'alias',a,None))
for ai,a in enumerate(names):
 for bi,b in enumerate(names):
    avail=max(availability[a],availability[b])
    if avail>=len(rows):continue
    for op in ('+','-','*'):
        if op in '+*' and bi<ai:continue
        sig=calc(op,values[a],values[b]);counts['shared_gate_forms']+=1
        if sig in needed:gate_matches.setdefault(sig,[]).append((avail,op,a,b))

candidates=[]
for sig in needed:
    items=requirements[sig]
    by_target={}
    for rec in items:by_target.setdefault(rec[0],[]).append(rec)
    targets=sorted(by_target)
    # A fixed new integer leaf has one residue per prime, shared over samples.
    constant=all(sig[k*SAMPLES+j]==sig[k*SAMPLES] for k in range(len(P)) for j in range(SAMPLES))
    if constant:counts['constant_leaf_signatures']+=1
    choices=gate_matches.get(sig,[])
    if not choices and not constant:continue
    counts['matching_signatures']+=1
    for ix,i in enumerate(targets):
     for j in targets[ix+1:]:
      counts['target_pairs']+=1
      # A replacement of the later target may use the earlier target, but
      # its inferred sample is still valid because the earlier is preserved.
      for first in by_target[i]:
       for second in by_target[j]:
        for shared in ([None] if constant else [])+[z for z in choices if z[0]<=i]:
         if shared is not None and (shared[2]==first[1] or shared[3]==first[1]):continue
         fresh=shared[2] if shared is not None and shared[1]=='alias' else '__joint_shared__'
         mapping={}
         def resolve(x):return mapping.get(x,x)
         def rewrite(rec):
             _,name,kind,x=rec
             if kind=='alias':mapping[name]=fresh;return None
             x=resolve(x)
             return [name,'-',x,fresh] if kind=='r-' else [name,kind,fresh,x]
         new=[]
         for pos,row in enumerate(rows):
             if pos==i and shared is not None and shared[1]!='alias':new.append([fresh,shared[1],shared[2],shared[3]])
             updated=(rewrite(first) if pos==i else rewrite(second) if pos==j else
                      [row[0],row[1],resolve(row[2]),resolve(row[3])])
             if updated is not None:new.append(updated)
         size=live(new,resolve(output));counts['tested_replacements']+=1
         if size<original:
             candidates.append({'targets':[first[1],second[1]],'forms':[list(first[2:]),list(second[2:])],
                                'shared':None if shared is None else list(shared[1:]),
                                'constant_mod_primes':[sig[k*SAMPLES] for k in range(len(P))] if shared is None else None,
                                'live':size})
if control_mode:
    expected=['a','b'] if control_kind==['--alias-control'] else ['c','d']
    if not any(c['targets']==expected and c['live']==4 for c in candidates):
        raise RuntimeError('joint-sharing positive control not detected')
print(json.dumps({'source_sha256':PIN,'screen_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  'primes':P,'samples_per_prime':SAMPLES,'seed':SEED,'counts':counts,'candidates':candidates,
                  'control_mode':control_kind[0] if control_mode else None,
                  'scope':'two exact target rewrites including aliases via one prior-node binary gate or fixed integer leaf; modular filter'},
                 sort_keys=True,indent=2))
