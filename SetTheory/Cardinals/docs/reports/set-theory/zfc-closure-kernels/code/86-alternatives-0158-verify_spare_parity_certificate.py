#!/usr/bin/env python3
"""Independent replay of the finite graph and four-equation parity witness."""
import sys,json,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent;BASE=HERE.parent/'context_folds/recovered/64/baseline/context246';sys.path.insert(0,str(BASE/'code'))
from check_literal_instructions import program_sites
obj=json.loads((HERE/'spare_parity_audit.json').read_text());source=BASE/'sources/Prog254.v';sites=program_sites(source)
interval_path=HERE.parent/'context_folds/recovered/66/results/interval-invariants.json';inv=json.loads(interval_path.read_text())['invariants']
trie={}
for i,(pc,op,r)in enumerate(sites):
 node=trie
 for b in pc[:-1]:node=node.setdefault(b,{})
 node[pc[-1]]=i

def locate(prefix):
 node=trie;i=0
 while isinstance(node,dict):
  node=node[prefix[i]if i<len(prefix)else'0'];i+=1
 assert not any(b=='1'for b in prefix[i:])
 return node

def increment(prefix):
 j=len(prefix)-1
 while j>=0 and prefix[j]=='1':j-=1
 return prefix[:j]+'1'+'0'*(len(prefix)-j-1)if j>=0 else''

def strip(prefix,bit,count):
 j=len(prefix)
 while count and j:
  j-=1
  if prefix[j]==bit:count-=1
 return prefix[:j]

expected=[]
for u,((pc,op,r),v)in enumerate(zip(sites,inv)):
 if v is None or op=='CH':continue
 if op=='CI':steps=[(increment(pc),1^(1<<(r+1)),'increment')]
 elif op=='CD':
  steps=[]
  if v[r][0]==0:steps.append((increment(strip(pc,'0',1)),1,'zero_decrement'))
  if v[r][1]>0:steps.append((increment(pc),1<<(r+1),'positive_decrement'))
 elif op=='CB':steps=[(increment(strip(pc,'0',r)),0,'break')]
 else:assert op=='CC';steps=[(strip(pc,'1',r),0,'continue')]
 for pp,label,kind in steps:expected.append(dict(source=u,target=locate(pp),label=label,kind=kind,register=r))
assert expected==obj['edges_certificate']
pot={int(k):v for k,v in obj['potentials'].items()};parent={int(k):v for k,v in obj['parent_certificate'].items()};edges=expected
for u,value in pot.items():
 walk=set();v=u;acc=0
 while parent[v]is not None:
  assert v not in walk;walk.add(v);p,k=parent[v];edge=edges[k]
  assert {edge['source'],edge['target']}=={v,p};acc^=edge['label'];v=p
 assert pot[v]==0 and acc==value
constraints=[]
for k,edge in enumerate(edges):
 e=pot[edge['source']]^pot[edge['target']]^edge['label']
 if e:constraints.append(dict(edge=k,expression=e))
assert constraints==obj['constraints']
value=0
for i in obj['contradiction_constraints']:value^=constraints[i]['expression']
assert value==1
out=dict(status='PASS',independent_path_semantics=True,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),interval_sha256=hashlib.sha256(interval_path.read_bytes()).hexdigest(),verified_nodes=len(pot),verified_edges=len(edges),xor_of_witness_equations=value,claim='No affine spare-count parity invariant of the stated form is closed under all interval-admitted CFG edges.',scope=obj['scope'])
(HERE/'spare_parity_independent_replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
