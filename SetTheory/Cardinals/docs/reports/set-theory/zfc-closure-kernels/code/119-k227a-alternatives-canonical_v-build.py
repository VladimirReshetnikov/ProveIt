#!/usr/bin/env python3
"""Shorten the original equality-vacuity emitter to canonical formula vacuity.

Source-only build.  The ordinary logical proof is in canonical_v_proof.md;
no binary TM compiler or simulation is implicit in this source certificate.
"""
from pathlib import Path
from functools import cache
import argparse, hashlib, json, sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'verification'))
import source_tools as base
INPUT_SHA = 'c17ab40e032e79dca03eaa955a78dbcd65bd030795ecc232dc504aff1551cb20'
REPLACEMENTS = [
 '111010010011011011111', # push the native Eq(a,b) code
 '1110100100110111000', # push scalar c
 '1110100100110111001', # push the native Eq(a,b) code
]
PUSH_A = '111010010011011011111000'

def get(root,path):
 for b in path:root=root[int(b)]
 return root

def put(root,path,value):
 if not path:return value
 b=int(path[0]);out=list(root);out[b]=put(root[b],path[1:],value);return tuple(out)

def main():
 p=argparse.ArgumentParser();p.add_argument('--scalar',choices=['a','b','c'],default='a');p.add_argument('--out',type=Path,default=Path(__file__).resolve().parent/'canonical_v');a=p.parse_args()
 path=Path(__file__).resolve().parent/'baseline235_sites.json'
 raw=path.read_bytes();base.require(hashlib.sha256(raw).hexdigest()==INPUT_SHA,'wrong baseline235 source')
 old=base.tree(json.loads(raw));new=old;push_path={'a':PUSH_A,'b':'111010010011011011111001','c':REPLACEMENTS[1]}[a.scalar];push=get(old,push_path)
 base.require(base.boundary(push)==(0,0,False),'a push not closed')
 base.require(len(base.sites(push))==26,'a push wrong length')
 cert=[]
 oldrows=base.sites(old)
 for pref in REPLACEMENTS:
  replaced=get(old,pref)
  base.require(base.boundary(replaced)==(0,0,False),'replaced push not closed')
  span=[i for i,(s,*_)in enumerate(oldrows)if s.startswith(pref)]
  cert.append(dict(path=pref,old_leaf_interval=[min(span),max(span)+1],old_leaf_count=len(span),new_leaf_count=26,old_boundary=base.boundary(replaced),new_boundary=base.boundary(push)))
  new=put(new,pref,push)
 newrows=base.sites(new)
 base.require([v for v in oldrows if not any(v[0].startswith(p)for p in REPLACEMENTS)] == [v for v in newrows if not any(v[0].startswith(p)for p in REPLACEMENTS)],'outside changed paths differ')
 base.require([x['old_leaf_count']for x in cert]==[82,26,82],'wrong three exact macro blocks')
 base.require(get(old,REPLACEMENTS[0])==get(old,REPLACEMENTS[2]),'original equality builders differ')
 data=(json.dumps(newrows,separators=(',',':'))+'\n').encode()
 structures=[];indices={}
 def save(t):
  if t in indices:return indices[t]
  node=t if base.is_leaf(t)else tuple(save(x)for x in t)
  indices[t]=len(structures);structures.append(node);return indices[t]
 r=save(new)
 receipt=dict(status='SOURCE_ONLY_CANONICAL_V',old_source_sha256=INPUT_SHA,new_source_sha256=hashlib.sha256(data).hexdigest(),old_metrics=base.metrics(old),new_metrics=base.metrics(new),replacements=cert,push_scalar=a.scalar,push_path=push_path,old_logical_row='Eq(a,b) -> All_c Eq(a,b)',new_logical_row=f'dec({a.scalar}) -> All_{a.scalar} dec({a.scalar})',gate='c != a and c != b',all_other_logical_rows='rho1 through rho8, CP, native GIC and full membership vacuity unchanged',AX_parser='unchanged: old-cache GEN, y and u read fields, nine standalone rows plus gated bundle',instruction_saving=112,scope='Literal source construction; no binary runtime or new Lean endpoint established by this script.')
 a.out.mkdir(parents=True,exist_ok=True)
 (a.out/'sites_logical.json').write_bytes(data)
 (a.out/'source.json').write_text(json.dumps(dict(root=r,structures=structures),indent=2)+'\n')
 (a.out/'certificate.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
