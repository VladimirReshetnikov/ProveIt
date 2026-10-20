#!/usr/bin/env python3
"""Source-only census of published finite equality hits and register swaps.

Only published hit10 (and its register-swapped version) currently carries the
inherited all-natural source proof. Other hits are discovery experiments.
"""
from pathlib import Path
from functools import lru_cache
import json, sys, hashlib, argparse, itertools, time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source_work'));import rotation_search as r
sys.path.insert(0,str(ROOT/'baseline219/K219_Construction_2026-10-20/portable'))
import build_source219 as eq
s=r.s
def normal(n):return tuple(n) if isinstance(n[0],str)else(normal(n[0]),normal(n[1]))
def swap(n):
 if s.leaf(n):return(n[0],11-n[1])if n[0]in('CI','CD')and n[1]in(5,6)else n
 return swap(n[0]),swap(n[1])
def nodes(t):
 seen=set();stack=[t]
 while stack:
  n=stack.pop()
  if n in seen:continue
  seen.add(n)
  if not s.leaf(n):stack.extend(n)
 return seen
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--heterogeneous',action='store_true');ap.add_argument('--swaps',action='store_true');a=ap.parse_args()
 out=ROOT/'source218/equality_variants';out.mkdir(exist_ok=True,parents=True)
 old=s.tree(json.loads((ROOT/'baseline220/K220_Construction_2026-10-20/machine/sites220.json').read_text()))
 base=s.tree(json.loads((ROOT/'baseline219/K219_Construction_2026-10-20/machine/sites219.json').read_text()))
 table=r.b.read_table((ROOT/'baseline219/K219_Construction_2026-10-20/machine/k219.native.tm').read_bytes())
 groups,_=r.b.decoder_map(table,base);node_states={}
 for q,ns in groups.items():
  for n in ns:node_states.setdefault(n,set()).add(q)
 library=[]
 for i,n in enumerate(json.loads((ROOT/'baseline219/K219_Construction_2026-10-20/research/encoding/eq_clean_hits.json').read_text())):
  n=normal(n)
  for flipped,x in((False,n),(True,swap(n))):
   library.append(dict(hit=i,swapped=flipped,tree=x))
 oldpaths=[]
 def scan(n,p=''):
  if n==eq.OLD:oldpaths.append(p);return
  if not s.leaf(n):scan(n[0],p+'0');scan(n[1],p+'1')
 scan(old);assert len(oldpaths)==4
 records=[]
 for i,v in enumerate(library):
  tree=old
  for path in oldpaths:tree=s.replace(tree,path,v['tree'])
  live=nodes(tree);fixed=set().union(*(node_states.get(n,set())for n in live))
  fresh=sum(not s.leaf(n)and n not in node_states for n in live)
  rows=s.sites(tree);raw=s.compact(rows)
  folder=out/f'uniform{i:02d}';folder.mkdir(exist_ok=True)
  (folder/'sites.json').write_bytes(raw)
  record={k:v[k]for k in('hit','swapped')}
  record.update(index=i,source=str((folder/'sites.json').relative_to(ROOT)),sha256=hashlib.sha256(raw).hexdigest(),metrics=s.metrics(tree),
                bare_retained_role_cost=50+len(fixed)+fresh,
                macro_right_decrements=sum(op=='CD'and p.endswith('1')for p,op,arg in s.sites(v['tree'])),
                whole_terminal_six=sum(p.endswith('000000')for p,op,arg in rows),
                scope='Source-only finite-screened equality substitution; other than hit10, requires unbounded macro proof. Every output requires allocation and complete runtime.')
  (folder/'receipt.json').write_text(json.dumps(record,indent=2)+'\n');records.append(record)
 (out/'uniform_summary.json').write_text(json.dumps(dict(status='UNIFORM_SOURCE_CENSUS',variants=records,macro_paths=oldpaths),indent=2)+'\n')
 for x in sorted(records,key=lambda x:(x['bare_retained_role_cost'],x['metrics']['dag_nodes'])):
  print(x['index'],x['hit'],x['swapped'],x['metrics'],'bare',x['bare_retained_role_cost'],'rightCD',x['macro_right_decrements'],flush=True)
 # Emit a small exact-integer description for the heterogeneous C++ census.
 vals=[];interned={}
 def intern(n):
  if n in interned:return interned[n]
  v=(str(n[0]),n[1])if s.leaf(n)else(enc(n[0]),enc(n[1]))
  i=len(vals);vals.append(v);interned[n]=i;return i
 enc=intern
 enc(base);oldid=enc(old);variant_ids=[enc(v['tree'])for v in library]
 templates=[];hole=[0]
 def templ(n):
  if n==eq.OLD:
   x=('hole',hole[0]);hole[0]+=1
  elif eq.OLD not in nodes(n):x=('constant',enc(n))
  else:x=('pair',templ(n[0]),templ(n[1]))
  i=len(templates);templates.append(x);return i
 tr=templ(old)
 qindex={q:i for i,q in enumerate(sorted(groups))}
 static_roles={enc(n):sorted(qindex[q]for q in qs)for n,qs in node_states.items()}
 payload=dict(nodes=vals,variant_ids=variant_ids,templates=templates,root=tr,static_roles=static_roles,nondecoder=50)
 (out/'heterogeneous_input.json').write_text(json.dumps(payload,separators=(',',':'))+'\n')
 with(out/'heterogeneous_input.txt').open('w')as f:
  f.write(f'{len(vals)} {len(templates)} {tr} {len(qindex)}\n')
  for j,n in enumerate(vals):
   roles=static_roles.get(j,[])
   if isinstance(n[0],str):a1=-1;a2=0;op={'CD':1,'CI':2,'CB':3,'CC':4,'CH':5}[n[0]]
   else:a1,a2=n;op=0
   f.write(' '.join(map(str,[a1,a2,op,len(roles),*roles]))+'\n')
  for t in templates:f.write(' '.join(map(str,[{'constant':0,'hole':1,'pair':2}[t[0]],*t[1:]]))+'\n')
  f.write(' '.join(map(str,variant_ids))+'\n')
if __name__=='__main__':main()
