#!/usr/bin/env python3
"""Expand a pinned source-block DAG and apply its declared structural replacement."""
import hashlib,json
from pathlib import Path
def need(p,m):
 if not p:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def reconstruct(inputs):
 baseline=(inputs/'baseline_sites.json').read_bytes();need(sha(baseline)=='309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878','Changed baseline source')
 rows=json.loads(baseline);leaves={p:(op,arg)for p,op,arg in rows}
 def tree(p=''):return leaves[p]if p in leaves else(tree(p+'0'),tree(p+'1'))
 t=tree();recipe=json.loads((inputs/'source_patch.json').read_text());need(recipe['format']=='source-block-dag-v1','Wrong source format');path=recipe['replacement_path'];old=t
 for b in path:old=old[int(b)]
 need(sha(json.dumps(old,separators=(',',':')).encode())==recipe['old_subtree_sha256'],'Changed source patch precondition')
 nodes=[]
 for i,row in enumerate(recipe['structures']):
  if row[0]=='leaf':need(len(row)==3,'Malformed leaf');node=tuple(row[1:])
  else:need(row[0]=='pair'and len(row)==3 and all(type(k)is int and 0<=k<i for k in row[1:]),'Malformed pair');node=(nodes[row[1]],nodes[row[2]])
  nodes.append(node)
 def edit(n,p):
  if not p:return nodes[recipe['root']]
  z=list(n);b=int(p[0]);z[b]=edit(z[b],p[1:]);return tuple(z)
 def flatten(n,p=''):return[[p,*n]]if isinstance(n[0],str)else flatten(n[0],p+'0')+flatten(n[1],p+'1')
 out=(json.dumps(flatten(edit(t,path)),separators=(',',':'))+'\n').encode();need(sha(out)==recipe['expected_source_sha256'],'Reconstructed source checksum mismatch');return out
if __name__=='__main__':
 p=Path(__file__).resolve().parent;data=reconstruct(p/'inputs');(p/'results').mkdir(exist_ok=True);(p/'results/sites.json').write_bytes(data);print('EXACT_SOURCE_RECONSTRUCTION_PASS',sha(data))
