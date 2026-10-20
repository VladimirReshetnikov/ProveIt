#!/usr/bin/env python3
"""Incremental decoder compilation for exploratory source changes.
Adapted from ProveIt candidate-k222/code/stack_ab.py at c011e44b.
Decoder binding alone is not full source or runtime correctness.
"""
from pathlib import Path
from collections import Counter,defaultdict
import json,sys,argparse
from context import P,s,b

def compile_tree(table,old_src,new_src):
 groups,paths=b.decoder_map(table,old_src)
 node_state={n:q for q,ns in groups.items()for n in ns}
 live=set()
 def visit(n):
  if s.leaf(n) or n in live:return
  live.add(n);visit(n[0]);visit(n[1])
 visit(new_src)
 origins={}
 def walk(n,o):
  if s.leaf(n)or o is None or s.leaf(o):return
  if n!=o:origins.setdefault(n,o)
  walk(n[0],o[0]);walk(n[1],o[1])
 walk(new_src,old_src)
 origins={n:o for n,o in origins.items()if o not in live}
 compiled=dict(table);mapped=dict(node_state);mapped[new_src]=84
 claimed={84:new_src};fresh=max(300,max(q for q,bit in table)+1);nextfresh=fresh;reused=0
 leaves={}
 for op in ['CI','CD','CC','CB','CH']:
  for arg in ([None]if op=='CH'else range(10)):
   ch=(op,arg)
   for bit in(0,1):
    choices=Counter(table[q,bit]for n,q in node_state.items()if n[bit]==ch)
    direct=[a for a in choices if a[:2]==(bit,1)]
    if len(direct)==1:leaves[ch,bit]=direct[0]
    elif ch==('CC',1)and bit==1:leaves[ch,bit]=(0,-1,1)
    elif ch==('CC',2)and bit==1:leaves[ch,bit]=(0,-1,16)
    elif ch==('CB',1)and bit==1:leaves[ch,bit]=(0,-1,40)
 def go(n):
  nonlocal fresh,reused
  if n in mapped:return mapped[n]
  if n in origins and origins[n]in node_state and len(groups[node_state[origins[n]]])==1 and node_state[origins[n]]not in claimed:
   q=node_state[origins[n]];reused+=1
  else:q=fresh;fresh+=1
  mapped[n]=q;claimed[q]=n
  for bit,ch in enumerate(n):
   if not s.leaf(ch):compiled[q,bit]=(bit,1,go(ch))
   elif n in origins and origins[n]in node_state and origins[n][bit]==ch:
    compiled[q,bit]=table[node_state[origins[n]],bit]
   elif(ch,bit)in leaves:compiled[q,bit]=leaves[ch,bit]
   else:raise ValueError(('no leaf action',ch,bit,q))
  return q
 for bit,ch in enumerate(new_src):
  compiled[84,bit]=(bit,1,go(ch))if not s.leaf(ch)else leaves[ch,bit]
 todo=[0];reach={0}
 for q in todo:
  for bit in(0,1):
   z=compiled[q,bit][2]
   if z!=254 and z not in reach:reach.add(z);todo.append(z)
 compiled={k:v for k,v in compiled.items()if k[0]in reach}
 gg,pp=b.decoder_map(compiled,new_src)
 for q,ns in gg.items():
  for n in ns:
   if mapped.get(n)!=q:raise ValueError(('node binding mismatch',q,mapped.get(n)))
 return compiled,dict(working_states=len(compiled)//2,fresh=fresh-nextfresh,reused=reused,aliases=sum(len(ns)-1 for ns in gg.values()),decoder_states=len(gg),interior_nodes=sum(len(ns)for ns in gg.values()))

def main():
 ap=argparse.ArgumentParser();ap.add_argument('sites',type=Path);ap.add_argument('out',type=Path);ap.add_argument('--old-sites',type=Path,default=P.parent/'machine/sites221.json');ap.add_argument('--old-table',type=Path,default=P.parent/'machine/k221.native.tm');args=ap.parse_args()
 old=s.tree(json.loads(args.old_sites.read_text()));new=s.tree(json.loads(args.sites.read_text()));T=b.read_table(args.old_table.read_bytes());TT,m=compile_tree(T,old,new)
 args.out.mkdir(parents=True,exist_ok=True);(args.out/'candidate.tm').write_bytes(b.table_bytes(TT));(args.out/'sites.json').write_bytes(s.compact(s.sites(new)));(args.out/'compile.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps(m))
if __name__=='__main__':main()
