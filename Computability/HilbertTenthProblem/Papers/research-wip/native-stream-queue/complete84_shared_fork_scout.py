#!/usr/bin/env python3
"""Finite two-output, shared-fork arithmetic scout; parent read as inert data."""
import argparse, hashlib, itertools, json, random
from collections import Counter
from pathlib import Path

PINS={
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade'}
FINAL={'norm_pair','norm_triple','norm_four','norm_product','all_units','seven_units','polynomial'}
MODS=(1000000007,1000000009,998244353)
def require(ok,why):
 if not ok:raise ValueError(why)
def parse(path):
 def obj(xs):
  d={}
  for k,v in xs:
   require(k not in d,'duplicate JSON key');d[k]=v
  return d
 def invalid(x):raise ValueError('nonfinite JSON')
 return json.loads(path.read_text(),object_pairs_hook=obj,parse_constant=invalid)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def digest(data):return hashlib.sha256(data).hexdigest()

def build(root):
 for name,pin in PINS.items():require(digest((root/name).read_bytes())==pin,'pin '+name)
 receipt=parse(root/'complete84_scaled_strong_output.json');packet=receipt['packet'];rows=packet['source'];by={r[0]:r for r in rows}
 require(len(rows)==84 and len(by)==84,'84 distinct rows')
 require(receipt['source_sha256']==PINS['complete84_scaled_strong_output.py'],'parent self pin')
 targets=[r[0] for r in rows if r[0] not in FINAL];require(len(targets)==77,'77 producer targets')
 targetbit={x:1<<i for i,x in enumerate(targets)}
 ancestors={x:0 for x in packet['free']}
 for name,op,a,b in rows:
  require(op in '+-*' and all(type(x)is int or type(x)is str and x in ancestors for x in (a,b)),'closed source')
  ancestors[name]=targetbit.get(name,0)|(ancestors.get(a,0) if type(a)is str else 0)|(ancestors.get(b,0) if type(b)is str else 0)
 # Original ports/registers and precisely six small constants. Later registers
 # are permitted only if independent of both replaced producer definitions.
 leaves=packet['free']+[r[0] for r in rows]+[-1,0,1,2,3,4]
 require(len(leaves)==len(set(leaves)),'distinct leaves')
 masks=[ancestors.get(x,0) if type(x)is str else 0 for x in leaves]
 rng=random.Random(840020031);samples=[];envs=[]
 for mod in MODS:
  while True:
   values={x:rng.randrange(2,98) for x in packet['free']};env=dict(values)
   for name,op,a,b in rows:
    aa=env[a] if type(a)is str else a;bb=env[b] if type(b)is str else b
    env[name]=(aa*bb if op=='*' else aa+bb if op=='+' else aa-bb)%mod
   if all(env[t]!=0 for t in targets):break
  samples.append({'modulus':mod,'free_values':values});envs.append(env)
 fingerprints=[tuple(env[x] if type(x)is str else x%mod for env,mod in zip(envs,MODS)) for x in leaves]
 leaf_index={}
 for i,fp in enumerate(fingerprints):leaf_index.setdefault(fp,[]).append(i)
 tfp={t:tuple(env[t] for env in envs) for t in targets};target_index={}
 for t,fp in tfp.items():target_index.setdefault(fp,[]).append(t)
 require(len(target_index)==len(targets),'pairwise distinct target fingerprints')
 for t,fp in tfp.items():
  require(all(masks[i]&targetbit[t] for i in leaf_index.get(fp,[])),'no independent existing-leaf alias '+t)
 def opfp(op,a,b):return tuple((x*y if op=='*' else x+y if op=='+' else x-y)%p for x,y,p in zip(a,b,MODS))
 def live_cost(shared,ta,ba,tb,bb):
  # shared=('alias',leaf_index) or (op,left_index,right_index).
  # A branch is None (alias shared), or (op,leaf_index,shared_is_left);
  # leaf_index=None denotes op(shared,shared).
  replacements={ta:ba,tb:bb};seen=set();todo=[packet['output']];count=0
  while todo:
   x=todo.pop()
   if type(x)is int or x in seen:continue
   seen.add(x)
   if x=='$shared':
    if shared[0]=='alias':todo.append(leaves[shared[1]])
    else:count+=1;todo.extend([leaves[shared[1]],leaves[shared[2]]])
   elif x in replacements:
    branch=replacements[x];todo.append('$shared')
    if branch is not None:
     count+=1
     if branch[1] is not None:todo.append(leaves[branch[1]])
   elif x in by:count+=1;todo.extend(by[x][2:])
  return count
 totals=Counter();hist=Counter();lower=[];best=84;best_witness=None;pair_results={}
 def examine(shared,fp,dependency_mask):
  nonlocal best,best_witness
  totals['shared_schedules']+=1
  hits={}
  for t in target_index.get(fp,[]):hits[t]=[None]
  for op in ('+','-','*'):
   for t in target_index.get(opfp(op,fp,fp),[]):hits.setdefault(t,[]).append((op,None,True))
  inverse=tuple(pow(z,-1,p) for z,p in zip(fp,MODS)) if all(fp) else None
  for t,goal in tfp.items():
   # T=u+l, u-l, l-u, or u*l. Commutative branch operand duplicates
   # are omitted, but every colliding original leaf is retained.
   requests=[('+',opfp('-',goal,fp),True),('-',opfp('-',fp,goal),True),('-',opfp('+',goal,fp),False)]
   if inverse is not None:requests.append(('*',tuple(x*y%p for x,y,p in zip(goal,inverse,MODS)),True))
   else:totals['zero_shared_multiplication_rejections']+=1
   for op,wanted,left in requests:
    for i in leaf_index.get(wanted,[]):hits.setdefault(t,[]).append((op,i,left))
  keys=list(hits)
  for ia,ta in enumerate(keys):
   for tb in keys[ia+1:]:
    pairmask=targetbit[ta]|targetbit[tb]
    if dependency_mask&pairmask:continue
    for ba in hits[ta]:
     if ba is not None and ba[1] is not None and masks[ba[1]]&pairmask:continue
     for bb in hits[tb]:
      if bb is not None and bb[1] is not None and masks[bb[1]]&pairmask:continue
      cost=live_cost(shared,ta,ba,tb,bb);totals['matching_acyclic_pair_schedules']+=1;hist[cost]+=1
      key=tuple(sorted([ta,tb]));record=pair_results.setdefault(key,[0,84]);record[0]+=1;record[1]=min(record[1],cost)
      if cost<best:best=cost;best_witness=[shared,ta,ba,tb,bb]
      if cost<84:lower.append({'shared':shared,'targets':[ta,tb],'branches':[ba,bb],'live_cost':cost})
 for i,fp in enumerate(fingerprints):examine(('alias',i),fp,masks[i]);totals['shared_aliases']+=1
 for i,a in enumerate(fingerprints):
  for j,b in enumerate(fingerprints):
   for op in ('+','-','*'):
    if op!='-' and j<i:continue
    examine((op,i,j),opfp(op,a,b),masks[i]|masks[j]);totals['shared_binary_gates']+=1
 return {'status':'PASS','source_sha256':digest(Path(__file__).read_bytes()),'parent_pins':PINS,'complete_parent_packet':packet,'grammar':{'targets':targets,'leaves':leaves,'shape':'shared alias or one binary gate; two distinct producer outputs, each aliasing shared, op(shared,shared), or one binary gate between shared and one original leaf','later_independent_registers_permitted':True,'max_new_gates':3,'constants':[-1,0,1,2,3,4],'operations':['+','-','*'],'all_target_pairs':len(targets)*(len(targets)-1)//2,'acyclicity':'every original leaf is independent of both replaced target definitions','count':'named replacement schedules with backward liveness from complete output; no unrestricted CSE or later algebraic folding' },'samples':samples,'fingerprint_guards':{'targets_nonzero_in_each_field':True,'targets_pairwise_distinct':True,'no_independent_existing_leaf_alias':True},'totals':dict(totals),'live_cost_histogram':{str(k):v for k,v in sorted(hist.items())},'pair_results':[{'targets':list(k),'matches':v[0],'minimum_including_parent':v[1]} for k,v in sorted(pair_results.items())],'minimum_including_parent':best,'lower_cost_fingerprint_matches':lower,'best_witness':best_witness,'scope':'Finite exact rejection certificate only; no arbitrary constants, fourth new gate, chained second output, coordinate changes or positive-zero identities.'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--expect',type=Path);g.add_argument('--output',type=Path);a=ap.parse_args();result=build(a.root)
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:require(exact(result,parse(a.expect)),'exact receipt replay')
 print(json.dumps({'totals':result['totals'],'minimum':result['minimum_including_parent'],'lower_cost_matches':len(result['lower_cost_fingerprint_matches'])}))
if __name__=='__main__':main()
