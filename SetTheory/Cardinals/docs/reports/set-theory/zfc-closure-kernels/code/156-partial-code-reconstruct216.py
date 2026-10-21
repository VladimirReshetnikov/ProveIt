#!/usr/bin/env python3
"""Deterministically reconstruct exact source and tables, without search or solver."""
from pathlib import Path
import argparse,json,hashlib
from functools import cache
import source_equivalence as s
ROOT=Path(__file__).resolve().parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 t={}
 for line in p.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,z=line.split();key=int(q),int(b);assert key not in t;t[key]=(int(w),d,int(z))
 return t
def serialize(t,order):return '#! start 0\n'+''.join(f'{q} {b} {t[q,b][0]} {t[q,b][1]} {t[q,b][2]}\n'for q in order for b in(0,1))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
 recipe=json.loads((ROOT/'source/dag_recipe.json').read_text());old=a.parent/'machine/sites217.json';assert sha(old)==recipe['baseline_sha256']
 nodes=[];ids={}
 def intern(n):
  if n not in ids:ids[n]=len(nodes);nodes.append(n)
  return ids[n]
 def freeze(n):return intern(n if s.leaf(n)else(freeze(n[0]),freeze(n[1])))
 assert freeze(s.tree(json.loads(old.read_text())))==recipe['baseline_root'];assert len(nodes)==recipe['baseline_nodes']
 for n in recipe['new_nodes']:
  assert len(n)==2 and all(type(x)is int and 0<=x<len(nodes)for x in n);nodes.append(tuple(n))
 @cache
 def thaw(i):return nodes[i]if s.leaf(nodes[i])else tuple(thaw(j)for j in nodes[i])
 rows=s.sites(thaw(recipe['candidate_root']));compact=s.compact(rows);spaced=json.dumps(rows).encode()
 assert hashlib.sha256(compact).hexdigest()==recipe['candidate_canonical_sha256'];assert hashlib.sha256(spaced).hexdigest()==recipe['candidate_sha256']
 (a.out/'sites216.json').write_bytes(spaced);(a.out/'sites216.compact.json').write_bytes(compact)
 tr=json.loads((ROOT/'source/table_recipe.json').read_text());p=a.parent/'machine/k217.native.tm';assert sha(p)==tr['parent_native_sha256'];t=table(p)
 assert len({(r[0],r[1])for r in tr['replacement_rows']})==len(tr['replacement_rows'])
 for q,b,w,d,z in tr['replacement_rows']:assert(q,b)in t;t[q,b]=(w,d,z)
 order=tr['native_serialization_order'];assert len(set(order))==217 and set(order)=={q for q,b in t}
 (a.out/'prefold217.native.tm').write_text(serialize(t,order));assert sha(a.out/'prefold217.native.tm')==tr['prefold_sha256']
 assert t[164,0]==(0,'R',77)and t[183,0]==(0,'R',150)and t[164,1]==t[183,1]==(1,'R',98)
 t={(q,b):(w,d,164 if z==183 else z)for(q,b),(w,d,z)in t.items()if q!=183};t[164,0]=(0,'L',201)
 order=[q for q in order if q!=183];(a.out/'k216.native.tm').write_text(serialize(t,order))
 mp=json.loads((ROOT/'machine/canonicalization.json').read_text());m={int(k):v for k,v in mp['native_to_canonical'].items()}
 assert len(m)==217 and len(set(m.values()))==217 and m[0]==0 and m[254]==216
 dense={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in t.items()};assert {q for q,b in dense}==set(range(216))
 (a.out/'k216.tm').write_text(serialize(dense,range(216)))
 assert sha(a.out/'k216.native.tm')==mp['native_sha256'];assert sha(a.out/'k216.tm')==mp['canonical_sha256']
 print('EXACT_SOURCE_AND_TABLE_RECONSTRUCTION_PASS')
if __name__=='__main__':main()
