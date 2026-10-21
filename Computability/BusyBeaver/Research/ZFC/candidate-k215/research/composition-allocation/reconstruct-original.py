#!/usr/bin/env python3
"""Rebuild held215 source/table from accepted216 + literal recipes; no solver/runtime."""
from pathlib import Path
from functools import cache
import argparse,json,hashlib
import source_language as s
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in t;t[q,b]=(w,d,z)
 return t
def raw(t):return ('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();a.out.mkdir(exist_ok=False,parents=True);here=Path(__file__).resolve().parent
 r=json.loads((here/'dag_recipe.json').read_text());p=a.parent/'sites216.json';assert sha(p)==r['parent_source_sha256'];nodes=[];ids={}
 def intern(n):
  if n in ids:return ids[n]
  enc=n if s.leaf(n)else(intern(n[0]),intern(n[1]));ids[n]=len(nodes);nodes.append(enc);return ids[n]
 assert intern(s.tree(json.loads(p.read_text())))==r['parent_root'] and len(nodes)==r['parent_nodes']
 for n in r['new_nodes']:
  assert len(n)==2 and all(type(x)is int and 0<=x<len(nodes)for x in n);nodes.append(tuple(n))
 @cache
 def thaw(i):return nodes[i]if s.leaf(nodes[i])else tuple(thaw(x)for x in nodes[i])
 (a.out/'sites215.json').write_bytes(s.compact(s.sites(thaw(r['candidate_root']))));assert sha(a.out/'sites215.json')==r['candidate_source_sha256']
 r=json.loads((here/'table_recipe.json').read_text());p=a.parent/'k216.native.tm';assert sha(p)==r['parent_native_sha256'];t=table(p)
 assert len({tuple(x[:2])for x in r['replacement_rows']})==len(r['replacement_rows'])
 for q,b,w,d,z in r['replacement_rows']:assert(q,b)in t;t[q,b]=(w,d,z)
 t={k:v for k,v in t.items()if k[0]not in r['removed_states']};assert sorted({q for q,b in t})==r['native_serialization_order'];assert len(t)==430
 (a.out/'k215.native.tm').write_bytes(raw(t));assert sha(a.out/'k215.native.tm')==r['candidate_native_sha256']
 r=json.loads((here/'canonicalization.json').read_text());m={int(k):v for k,v in r['native_to_canonical'].items()};assert len(m)==216 and len(set(m.values()))==216 and m[0]==0 and m[254]==215
 d={(m[q],b):(w,di,m[z])for(q,b),(w,di,z)in t.items()};assert{q for q,b in d}==set(range(215));inv={v:k for k,v in m.items()};assert{(inv[q],b):(w,di,inv[z])for(q,b),(w,di,z)in d.items()}==t
 (a.out/'k215.tm').write_bytes(raw(d));assert sha(a.out/'k215.tm')==r['canonical_sha256']
 print(json.dumps({'status':'EXACT_SOURCE_AND_TABLE_RECONSTRUCTION_PASS','states':215,'rows':430,'files':{p.name:sha(p)for p in a.out.iterdir()}},indent=2))
if __name__=='__main__':main()
