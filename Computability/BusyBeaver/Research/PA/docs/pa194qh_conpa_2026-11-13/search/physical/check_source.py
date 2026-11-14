#!/usr/bin/env python3
"""Check the closed-fragment scope and exact resolved source graph of seeds."""
from pathlib import Path
import hashlib,json,argparse
HERE=Path(__file__).resolve().parent
nodes=json.loads((HERE/'inputs/source_nodes.json').read_text())
def parse_grammar(path):
 g=json.loads(Path(path).read_text())
 def go(v):return [go(x)for x in g['rules'][v]]if isinstance(v,str)and v in g['rules']else v
 return go(g['root'])
def leaves(tree,path=(),ax=None):
 if isinstance(tree,str):return leaves(ax if tree=='x67' else nodes[tree],path,ax)
 if tree[0]=='leaf':return [(path,tree[1],tree[2])]
 return leaves(tree[0],path+(0,),ax)+leaves(tree[1],path+(1,),ax)
def closed(name):
 return all((op!='dec' or 0 in p)and(op!='continueTo' or p.count(1)>=a)and(op!='breakTo'or p.count(0)>=a)for p,op,a in leaves(name))
def instructions(ax):
 ss=leaves('node172',ax=ax);first={};exact={p:i for i,(p,op,a)in enumerate(ss)}
 for i,(p,op,a)in enumerate(ss):
  for k in range(len(p)+1):first.setdefault(p[:k],i)
 def locate(p):
  if p in first:return first[p]
  while p and not p[-1]:
   p=p[:-1]
   if p in exact:return exact[p]
  raise ValueError(('locate',p))
 def after(p):
  for k in range(len(p)-1,-1,-1):
   if p[k]==0:return locate(p[:k]+(1,))
  raise ValueError(('after',p))
 def cut(p,b,n):
  for k in range(len(p)-1,-1,-1):
   if p[k]==b:
    n-=1
    if n==0:return p[:k]
  raise ValueError(('cut',p,b,n))
 out=[]
 for p,op,a in ss:
  if op=='inc':out.append(['inc',a,after(p)])
  elif op=='dec':out.append(['dec',a,after(cut(p,0,1)),after(p)])
  elif op=='breakTo':out.append(['jump',after(cut(p,0,a))])
  elif op=='continueTo':out.append(['jump',locate(cut(p,1,a))])
  elif op=='halt':out.append(['halt'])
  else:raise ValueError(op)
 return out
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('grammars',nargs='*',type=Path);args=ap.parse_args()
 reference=json.loads((HERE/'inputs/pa194.instructions.json').read_text());assert instructions(parse_grammar(HERE/'inputs/pa194.grammar.json'))==reference
 atoms=['node49','node54','node57','node69','node17','node64','node37','node48'];assert all(closed(n)for n in atoms)
 checked=[]
 for path in args.grammars:
  ins=instructions(parse_grammar(path));okay=ins==reference
  checked.append({'path':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'source_sites':len(ins),'exact_resolved_source_graph':okay})
  assert okay,path
 print(json.dumps({'closed_fragments':atoms,'source_sites':len(reference),'grammar_checks':checked,'scope':'Exact source binding only; does not certify literal tape execution of changed grammars.'},indent=2))
