#!/usr/bin/env python3
"""Change DP fixed base to the widened splice and expose one more closed layer."""
from pathlib import Path
import json,sys,hashlib
sys.dont_write_bytecode=True
import source_language as s,measure_pinned as m
P=Path(__file__).resolve().parent;plan=json.loads((P/'input.json').read_text());original=s.tree(json.loads((Path(plan['seed'])/'sites218.json').read_text()))
nodes=[];ids={}
for i,r in enumerate(plan['nodes']):
 t=tuple(r['leaf'])if'leaf'in r else tuple(nodes[x]for x in r['children']);nodes.append(t);ids[t]=i
H0=('HOLE',0);H1=('HOLE',1);skeleton=m.splice(s,m.splice(s,original,648,4433,H1),135,486,H0)
def forest(n,lo,hi,i=0):
 j=i+len(m.flat(n))
 if j<=lo or i>=hi:return[]
 if lo<=i and j<=hi:return[n]
 return forest(n[0],lo,hi,i)+forest(n[1],lo,hi,i+len(m.flat(n[0])))
def lead(t):return 0 if s.leaf(t)else 1+lead(t[0])
def split(t):
 assert s.boundary(t)==(0,0,False)
 if lead(t)<=5:return[t]
 assert not s.leaf(t)and s.boundary(t[0])==s.boundary(t[1])==(0,0,False)
 return split(t[0])+split(t[1])
def finer(ts):
 out=[]
 for t in ts:
  if not s.leaf(t)and s.boundary(t[0])==s.boundary(t[1])==(0,0,False):out.extend(t)
  else:out.append(t)
 return out
prefix=finer(sum((split(t)for t in forest(original,648,1474)),[]));suffix=finer(sum((split(t)for t in forest(original,1773,4433)),[]));base=set()
def fixed(t):
 if t in(H0,H1):return
 if t in ids:base.add(ids[t])
 if not s.leaf(t):fixed(t[0]);fixed(t[1])
fixed(skeleton)
for t in prefix+suffix:fixed(t)
words=sorted(plan['recipes']);reused=plan['reused_old_closed_subtree_patterns'];lines=[f'{len(nodes)} 0 {len(words)} {len(reused)} {len(base)} {plan["old_node_count"]} 4 6 30\n']
for i,row in enumerate(plan['nodes']):
 l,r=row.get('children',[-1,-1]);lines.append(f'{l} {r} {int(i in base)}\n')
lines.append(' '.join(str(plan['macro_ids'][k])for k in'abcFIQ')+'\n');lines.extend(w+'\n'for w in words);lines.extend(f'{r["word"]} {r["node"]}\n'for r in reused)
(P/'input-v3.txt').write_text(''.join(lines));rec={'base_nodes':sorted(base),'prefix_ids':[ids[t]for t in prefix],'suffix_ids':[ids[t]for t in suffix],'beam':4,'zero_limit':6,'deadline_seconds':30,'input_sha256':hashlib.sha256((P/'input-v3.txt').read_bytes()).hexdigest(),'change':'Updated fixed-base accounting for widened closed splice and one further split of fixed closed factors; all old source bytes and macro words unchanged.'};(P/'input-v3.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec)
