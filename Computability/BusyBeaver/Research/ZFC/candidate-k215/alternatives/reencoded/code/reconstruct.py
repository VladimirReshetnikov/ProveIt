#!/usr/bin/env python3
"""Reconstruct the alternative table and source from the exact included parent."""
from pathlib import Path
from functools import cache
import argparse,json,hashlib
import source_tools as s
ROOT=Path(__file__).resolve().parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 t={}
 for line in p.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert (q,b)not in t and b in(0,1)and w in(0,1)and d in('L','R');t[q,b]=(w,d,z)
 return t
def serial(t):return '#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))
def reconstruct(parent,out):
 out.mkdir(parents=True,exist_ok=True);recipe=json.loads((ROOT/'source/dag_recipe.json').read_text());p=parent/'source/sites215.compact.json';assert sha(p)==recipe['parent_source_sha256'];nodes=[];ids={}
 def freeze(n):
  z=n if s.leaf(n)else(freeze(n[0]),freeze(n[1]))
  if z not in ids:ids[z]=len(nodes);nodes.append(z)
  return ids[z]
 assert freeze(s.tree(json.loads(p.read_text())))==recipe['parent_root']and len(nodes)==recipe['parent_nodes']
 for n in recipe['new_nodes']:
  assert len(n)==2 and all(type(x)is int and 0<=x<len(nodes)for x in n);nodes.append(tuple(n))
 @cache
 def thaw(n):return nodes[n]if s.leaf(nodes[n])else tuple(thaw(j)for j in nodes[n])
 (out/'sites215.json').write_bytes(s.compact(s.sites(thaw(recipe['candidate_root']))));assert sha(out/'sites215.json')==recipe['candidate_source_sha256']
 r=json.loads((ROOT/'source/table_recipe.json').read_text());p=parent/'machine/k215.native.tm';assert sha(p)==r['parent_native_sha256'];T=table(p);keys=set()
 for q,b,ow,od,oz,nw,nd,nz in r['replacement_rows']:
  assert(q,b)not in keys and T[q,b]==(ow,od,oz);keys.add((q,b));T[q,b]=(nw,nd,nz)
 assert len(keys)==17 and len(T)==430;order=[tuple(x)for x in r['native_row_order']];assert len(order)==len(set(order))==len(T)and set(order)==set(T);(out/'k215.native.tm').write_text('#! start 0\n'+''.join(f'{q} {b} {T[q,b][0]} {T[q,b][1]} {T[q,b][2]}\n'for q,b in order));assert sha(out/'k215.native.tm')==r['candidate_native_sha256']
 m=json.loads((ROOT/'machine/canonicalization.json').read_text());cm={int(k):v for k,v in m['native_to_canonical'].items()};nm={v:int(k)for k,v in m['normalized_to_native'].items()}
 for name,mp in [('k215.tm',cm),('k215.normalized.tm',nm)]:
  assert len(mp)==len(set(mp.values()))==216;(out/name).write_text(serial({(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T.items()}))
 return T
def main():
 if not __debug__:raise RuntimeError('Run Python with assertions enabled')
 ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();reconstruct(a.parent,a.out);print('EXACT_ALTERNATIVE215_RECONSTRUCTION_PASS')
if __name__=='__main__':main()
