#!/usr/bin/env python3
"""Exact bounded enumeration with modular refutations; no Lean."""
from pathlib import Path
from hashlib import sha256
from collections import defaultdict
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
ROOT=Path(__file__).resolve().parents[2]; D=Path(__file__).resolve().parent
for path,h in json.loads((D/'pins.json').read_text()).items(): assert sha256((ROOT/path).read_bytes()).hexdigest()==h,path
vectors=json.loads((D/'vectors.json').read_text()); P=1000003; W=8
assert P>1 and all(P%d for d in range(2,int(P**0.5)+1))

def apply(op,a,b):
 return tuple((x+y if op=='+' else x-y if op=='-' else x*y)%P for x,y in zip(a,b))

def indexed(pool,values,target):
 """Exactly the triples surviving coordinate 0 of the full ordered search."""
 index=defaultdict(list)
 for y in pool:index[values[y][0]].append(y)
 found=[];t=target[0]
 for x in pool:
  v=values[x][0]
  for op,key in (('+',(t-v)%P),('-',(v-t)%P),('*',t*pow(v,-1,P)%P if v else None)):
   ys=pool if op=='*' and v==0 and t==0 else ([] if key is None else index[key])
   for y in ys:found.append((op,x,y))
 return found

def brute(pool,values,target):
 return [(op,x,y) for x in pool for y in pool for op in '+-*' if apply(op,values[x],values[y])[0]==target[0]]
# Explicitly test the special zero multiplier and an ordinary nonzero case.
control={'zero':(0,)*W,'one':(1,)*W,'two':(2,)*W}
for t in [(0,)*W,(2,)*W]:assert sorted(indexed(list(control),control,t))==sorted(brute(list(control),control,t))
results={}
for path, rawvals in sorted(vectors.items()):
 g=json.loads((ROOT/path).read_text()); rows=g['source'];names=g['witnesses']+g['fixed_numerals']
 assert len(names)==17 and len(set(names))==17 and set(rawvals)==set(names)
 assert all(len(v)==W and all(isinstance(x,int) and 0<=x<P for x in v) for v in rawvals.values())
 values={k:tuple(v) for k,v in rawvals.items()}; values.update({str(i):(i,)*W for i in range(5)})
 assert not(set(names)&set(map(str,range(5))))
 consumer=defaultdict(set)
 for n,op,a,b in rows:
  assert op in '+-*'
  for x in (a,b):
   if isinstance(x,str):consumer[x].add(n)
 available=list(values);produced=set(); details=[]; total=first=0; survivors=[]; controls=0
 for n,op,a,b in rows:
  assert n not in values
  a,b=map(str,(a,b)); assert a in values and b in values
  target=apply(op,values[a],values[b]); dead={x for x in (a,b) if x in produced and consumer[x]=={n}}
  for d in sorted(dead):
   pool=[x for x in available if x!=d];tested=3*len(pool)**2;total+=tested
   candidates=indexed(pool,values,target); first+=len(candidates)
   if controls<5:
    assert sorted(candidates)==sorted(brute(pool,values,target));controls+=1
   witnesses=[];hit=[]
   for triple in candidates:
    actual=apply(triple[0],values[triple[1]],values[triple[2]])
    bad=next((i for i,(x,y) in enumerate(zip(actual,target)) if x!=y),None)
    witnesses.append({'replacement':list(triple),'first_counterexample_vector':bad})
    if bad is None:hit.append(list(triple))
   survivors.extend([[n,d]+t for t in hit]);details.append({'target':n,'deleted_predecessor':d,'pool_size':len(pool),'expressions':tested,'survive_first_vector':len(candidates),'first_vector_survivors':witnesses,'survive_all_vectors':len(hit)})
  values[n]=target;available.append(n);produced.add(n)
 assert g['output'] in produced and controls==5
 results[path]={'rows':len(rows),'exclusive_target_predecessor_pairs':len(details),'ordered_replacement_expressions':total,'survive_first_vector':first,'survivors':survivors,'brute_force_control_pairs':controls,'pairs':details}
print(json.dumps({'modulus':P,'vector_count':W,'vector_file':'vectors.json','constants':[0,1,2,3,4],'enumeration':'For each target and exclusive direct predecessor, all ordered pairs of earlier inputs/wires/constants excluding predecessor and each of +,-,*; optimized coordinate-0 lookup is exhaustive in the prime field and explicitly handles zero multiplication.','graphs':results,'scope':'Exact polynomial equality over arbitrary ports, not same-zero maps or fixed-port-only identities.','lean_executed':False},sort_keys=True,indent=2))
