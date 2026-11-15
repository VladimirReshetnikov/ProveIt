#!/usr/bin/env python3
"""Exact explicit-bijection matching against all 520 spanning corpus classes.

Allows arbitrary state names and roots, reflection, global symbol exchange,
and erased terminal-entry write/move decorations. Symbol exchange is an
additional structural screen, not zero-blank semantic equivalence.
"""
from pathlib import Path
import argparse,hashlib,json
import literal_inventory as lit
ROOT=Path(__file__).resolve().parent
def match(a,ar,b,br,mirror=False,flip=False):
 ra,sa,ha=a;rb,sb,hb=b
 if len(sa)!=len(sb):return None
 mapping={ar:br};reverse={br:ar};todo=[ar]
 for q in todo:
  p=mapping[q]
  for x in(0,1):
   w,d,t=ra[q,x];v,e,u=rb[p,x^flip]
   if(t==ha)!=(u==hb):return None
   if t==ha:continue
   if w!=(v^flip)or d!=(('L'if e=='R'else'R')if mirror else e):return None
   if t in mapping:
    if mapping[t]!=u:return None
   else:
    if u in reverse:return None
    mapping[t]=u;reverse[u]=t;todo.append(t)
 return mapping if len(mapping)==len(sa)else None
def spanning(a):
 rows,states,halt=a
 for root in sorted(states):
  seen={root};todo=[root]
  for q in todo:
   for x in(0,1):
    n=rows[q,x][2]
    if n!=halt and n not in seen:seen.add(n);todo.append(n)
  if len(seen)==len(states):return root
 return None
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('candidates',nargs='+',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 frontier=json.loads((ROOT/'census/frontier194.json').read_text());assert len(frontier)==520
 corpus=[]
 for r in frontier:
  p=ROOT/'census'/r['representative'];data=lit.parse_table(p.read_bytes());assert data
  corpus.append((r['table_class'],data,str(p.relative_to(ROOT))))
 out=[]
 for p in a.candidates:
  b=p.read_bytes();data=lit.parse_table(b);assert data
  root=spanning(data);assert root is not None
  matches=[];attempts=0
  for key,other,loc in corpus:
   found=None
   for reflection,complement in[(False,False),(True,False),(False,True),(True,True)]:
    if found:break
    for q in sorted(other[1]):
     attempts+=1;m=match(data,root,other,q,reflection,complement)
     if m is not None:
      found=dict(table_class=key,representative=loc,candidate_root=root,corpus_root=q,reflection=reflection,symbol_exchange=complement,bijection=m);break
   if found:matches.append(found)
  out.append(dict(candidate=p.name,sha256=hashlib.sha256(b).hexdigest(),states=len(data[1]),corpus_classes=len(corpus),rooted_match_attempts=attempts,matches=matches,structurally_new_to_corpus=not matches))
 result=dict(status='COMPLETE',scope=__doc__,results=out);a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
