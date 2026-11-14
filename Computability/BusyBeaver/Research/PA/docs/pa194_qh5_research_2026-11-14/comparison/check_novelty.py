#!/usr/bin/env python3
"""Exact finite graph novelty against the 77-class current 194-table corpus.

Compares full canonical tuples, allowing any spanning root, state renaming,
tape reflection, global symbol exchange, and arbitrary halt-edge effects.
One disconnected diagnostic table is structurally ineligible to match.
"""
from pathlib import Path
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parent.parent
def read(path):
 rows={}
 for line in path.read_text().splitlines():
  if not line.strip()or line.lstrip().startswith('#'):continue
  q,b,w,d,n=line.split();key=(int(q),int(b))
  assert key not in rows and d in('L','R')
  rows[key]=(int(w),0 if d=='L'else 1,int(n))
 states={q for q,b in rows}
 assert set(rows)=={(q,b)for q in states for b in(0,1)}
 assert all(w in(0,1)for w,d,n in rows.values())
 return rows,states
def canonical(rows,states):
 best=None;roots=0
 for root in sorted(states):
  index={root:0};order=[root];actions=[]
  for q in order:
   for b in(0,1):
    w,d,n=rows[q,b]
    if n in states:
     if n not in index:index[n]=len(order);order.append(n)
     actions.append((w,d,index[n]))
    else:actions.append((0,0,-1))
  if len(order)!=len(states):continue
  roots+=1;key=tuple(actions)
  if best is None or key<best:best=key
 return best,roots
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--candidate',type=Path,default=ROOT/'machine/machine.tm');p.add_argument('--output',type=Path,default=ROOT/'comparison/novelty.json');a=p.parse_args()
candidate,states=read(a.candidate);assert len(states)==194
keys=[]
for flip in(0,1):
 for mirror in(0,1):
  transformed={(q,b^flip):(w^flip,d^mirror,n)for(q,b),(w,d,n)in candidate.items()}
  key,roots=canonical(transformed,states);assert key is not None
  keys.append((flip,mirror,key,roots))
assert keys[0][2]==canonical(candidate,states)[0]
frontier=json.loads((ROOT/'comparison/frontier194_all.json').read_text())
matches=[];checks=[]
for entry in frontier:
 path=ROOT/'comparison'/entry['representative_file']
 assert sha(path)==entry['representative_sha256'],path
 table,controls=read(path);assert len(controls)==194
 key,roots=canonical(table,controls)
 variants=[{'flip':f,'reflection':m}for f,m,k,n in keys if key==k]
 if variants:matches.append({'name':entry['name'],'variants':variants})
 checks.append({'name':entry['name'],'table_class':entry['table_class'],
  'byte_sha256':sha(path),'spanning_roots':roots,'match':bool(variants)})
assert not matches,matches
receipt={'status':'PASS','snapshot':'2337ce611a26e308697ccbddb2a1636f989f01c3',
 'candidate_sha256':sha(a.candidate),'states':194,'compared_table_classes':len(frontier),
 'spanning_prior_classes':sum(x['spanning_roots']>0 for x in checks),
 'nonspanning_diagnostic_classes':sum(x['spanning_roots']==0 for x in checks),
 'full_tuple_comparison':True,'state_renaming':True,'arbitrary_spanning_root':True,
 'reflection':True,'global_symbol_exchange':True,'halt_edge_effects_ignored':True,
 'matches':matches,'self_match_positive_control':True,'checks':checks,
 'scope':'Recognized complete literal/array tables in all 61 filed packets, five incoming archives, PA source tree and retained nested archives. Parameterized unmaterialized machines and arbitrary code encodings are outside the census.'}
a.output.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k!='checks'},indent=2))
