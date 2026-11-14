from collections import defaultdict
from functools import lru_cache
import json,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
import search_directional as D
L=D.L

def islands(t,root):
 occ=defaultdict(set);seen=set();incoming=defaultdict(list)
 for(p,b),(_,_,q)in t.items():incoming[q].append((p,b))
 def visit(q,n):
  if(q,n)in seen:return
  seen.add((q,n));occ[q].add(n)
  if L.leaf(n):return
  for b in(0,1):
   w,d,z=t[q,b]
   if(w,d)==(b,1):visit(z,n[b])
 visit(84,root)
 def pure(q):return(q,0)in t and all(t[q,b][:2]==(b,1)for b in(0,1))
 roots=[]
 for q,ns in occ.items():
  if len(ns)!=1 or not pure(q):continue
  node=next(iter(ns))
  if L.boundary(node)!=(0,0,False):continue
  used=set();atoms=[]
  def collect(s,n,isroot=False):
   if (isroot or len(incoming[s])==1) and pure(s) and not L.leaf(n) and all(L.boundary(x)==(0,0,False)for x in n):
    used.add(s)
    for b in(0,1):collect(t[s,b][2],n[b])
   else:atoms.append((s,n))
  collect(q,node,True)
  if len(used)>1:roots.append((q,node,used,atoms))
 return occ,roots

if __name__=='__main__':
 b=D.I.base;t=D.I.read(b/'machine/variant_plain/u208.native.tm');ss=json.loads((b/'machine/variant_plain/u208.sites.json').read_text());root=L.tree(ss)
 occ,rs=islands(t,root)
 print([(q,len(es),[a for a,n in atoms])for q,n,es,atoms in rs])

def options(t,root):
 occ,roots=islands(t,root);all=[]
 for target,node,removed,atoms in roots:
  atom_nodes={n:i for i,(q,n)in enumerate(atoms)}
  @lru_cache(None)
  def word(n):
   if n in atom_nodes:return(atom_nodes[n],)
   if L.leaf(n):return None
   a,b=word(n[0]),word(n[1]);return a+b if a is not None and b is not None else None
  wanted=tuple(atom_nodes[n]for q,n in atoms);library={}
  for q,ns in occ.items():
   if q in removed or len(ns)!=1:continue
   n=next(iter(ns));w=word(n)
   if w is not None:library.setdefault(w,[]).append((q,n))
  donors=[(w,lib)for w,lib in library.items()if len(w)>1 and any(wanted[i:i+len(w)]==w for i in range(len(wanted)-len(w)+1))]
  if donors:all.append((target,node,removed,atoms,wanted,library,donors))
 return all
