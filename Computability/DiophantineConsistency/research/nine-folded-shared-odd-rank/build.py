#!/usr/bin/env python3
"""Share the literal stored RankPlusOne in B1; preserve the complete polynomial."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
PARENT=HERE.parent/'nine-folded-minimal-reflection'

def need(ok,text):
 if not ok:raise ValueError(text)
def digest(raw):return sha256(raw).hexdigest()
def encoded(obj):return(json.dumps(obj,indent=2,sort_keys=True)+'\n').encode()

def build(profile):
 path=PARENT/(profile+'.json');parent=json.loads(path.read_bytes());old=parent['nodes'];nodes=[];mapping={}
 B1=parent['named_nodes']['B1'];b=old[B1];need(b['kind']=='add','literal oddrank addition')
 one=b['left'];need(old[one]==dict(kind='literal',value=1),'odd rank plusone')
 twice=b['right'];need(old[twice]['kind']=='mul','literal twiceR product')
 two,R=old[twice]['left'],old[twice]['right'];need(old[two]==dict(kind='literal',value=2),'exact scalar2')
 need(old[R]['kind']=='sub'and old[R]['right']==one,'actual R equals stored RankPlusOne minus1');rp1=old[R]['left']
 need([i for i,n in enumerate(old)if n['kind']in['add','sub','mul']and twice in[n['left'],n['right']]]==[B1],'entire private2R consumer inventory')
 def app(node):nodes.append(node);return len(nodes)-1
 def clone(i):
  if i in mapping:return mapping[i]
  if i==B1:
   mapping[i]=app(dict(kind='add',left=clone(R),right=clone(rp1)));return mapping[i]
  node=dict(old[i])
  if node['kind']in['add','sub','mul']:node.update(left=clone(node['left']),right=clone(node['right']))
  mapping[i]=app(node);return mapping[i]
 output=clone(parent['output']);need(set(range(len(old)))-set(mapping)=={twice},'only private2R node removed')
 labels={n:mapping[i]for n,i in parent['named_nodes'].items()};labels['sourceRank']=mapping[R];labels['sourceRankPlusOne']=mapping[rp1]
 counts=dict(Counter(n['kind']for n in nodes if n['kind']in['add','sub','mul']))
 degrees=[]
 for node in nodes:
  k=node['kind'];degrees.append(1 if k=='variable'else 0 if k in['literal','fixed']else
      degrees[node['left']]+degrees[node['right']]if k=='mul'else max(degrees[node['left']],degrees[node['right']]))
 data=dict(parent)
 data.update(schema='nine_folded_shared_odd_rank_v1',parent=str(path.relative_to(BASE)),parent_sha256=digest(path.read_bytes()),
  nodes=nodes,output=output,parent_clone_map={str(k):v for k,v in mapping.items()},
  deleted_parent_nodes=[twice],changed_parent_nodes=[B1],inserted_child_nodes=[],named_nodes=labels,
  operation_counts=counts,total_operations=sum(counts.values()),syntactic_degree=degrees[output],degree_upper_bound=degrees[output],
  named_degrees={n:degrees[i]for n,i in labels.items()},
  algebraic_rewrite='Entire polynomial pointwise equal to parent by B1=R+RankPlusOne, using literal R=RankPlusOne-1.')
 return data

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
 for profile in['boundary_simple','compact_simple']:
  data=build(profile);raw=encoded(data);p=HERE/(profile+'.json')
  if args.check:need(p.read_bytes()==raw,'complete deterministic graph '+profile)
  else:p.write_bytes(raw)
  print(profile,data['total_operations'],data['operation_counts'],data['exact_degree'],data['syntactic_degree'])
if __name__=='__main__':main()
