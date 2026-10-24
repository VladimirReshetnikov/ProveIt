#!/usr/bin/env python3
"""New reflected-parameter nine-positive siblings; never executes a parent emitter."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
PARENT=HERE.parent/'nine-folded-saturation-tight'

def need(ok,text):
 if not ok:raise ValueError(text)
def digest(raw):return sha256(raw).hexdigest()
def encoded(obj):return(json.dumps(obj,indent=2,sort_keys=True)+'\n').encode()

def build(profile):
 path=PARENT/(profile+'.json');parent=json.loads(path.read_bytes());old=parent['nodes'];nodes=[];mapping={};newlambda=None
 def app(node):nodes.append(node);return len(nodes)-1
 def op(k,a,b):return app(dict(kind=k,left=a,right=b))
 def clone(i):
  nonlocal newlambda
  if i in mapping:return mapping[i]
  if i==parent['named_nodes']['G']:
   A,F,C=[clone(parent['named_nodes'][n])for n in['A','F','C']]
   one=clone(next(j for j,n in enumerate(old)if n==dict(kind='literal',value=1)))
   newlambda=op('add',op('add',A,C),one)
   mapping[i]=op('sub',op('mul',F,newlambda),A);return mapping[i]
  node=dict(old[i])
  if node['kind']in['add','sub','mul']:node.update(left=clone(node['left']),right=clone(node['right']))
  mapping[i]=app(node);return mapping[i]
 output=clone(parent['output'])
 labels={n:(newlambda if n=='Lambda'else mapping[i])for n,i in parent['named_nodes'].items()}
 counts=dict(Counter(n['kind']for n in nodes if n['kind']in['add','sub','mul']))
 degrees=[]
 for node in nodes:
  k=node['kind'];degrees.append(1 if k=='variable'else 0 if k in['literal','fixed']else
      degrees[node['left']]+degrees[node['right']]if k=='mul'else max(degrees[node['left']],degrees[node['right']]))
 data=dict(parent)
 data.update(schema='nine_folded_reflected_parameter_v1',parent=str(path.relative_to(BASE)),parent_sha256=digest(path.read_bytes()),
  nodes=nodes,output=output,parent_clone_map={str(k):v for k,v in mapping.items()},
  deleted_parent_nodes=sorted(set(range(len(old)))-set(mapping)),changed_parent_nodes=[parent['named_nodes']['G']],
  inserted_child_nodes=sorted(set(range(len(nodes)))-set(mapping.values())),named_nodes=labels,
  operation_counts=counts,total_operations=sum(counts.values()),exact_degree=parent['exact_degree']-2,
  expected_exact_degree=parent['exact_degree']-2,syntactic_degree=degrees[output],degree_upper_bound=degrees[output],
  named_degrees={n:degrees[i]for n,i in labels.items()},
  algebraic_rewrite='Existential reflection at auxiliary parameter: G=F*(A+C+1)-A; not pointwise parent polynomial equality.')
 data.pop('core_clone_map',None)
 return data

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
 for profile in['boundary_simple','compact_simple']:
  data=build(profile);raw=encoded(data);p=HERE/(profile+'.json')
  if args.check:need(p.read_bytes()==raw,'complete deterministic graph '+profile)
  else:p.write_bytes(raw)
  print(profile,data['total_operations'],data['operation_counts'],data['exact_degree'],data['syntactic_degree'])
if __name__=='__main__':main()
