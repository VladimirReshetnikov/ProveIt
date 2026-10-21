#!/usr/bin/env python3
"""Commute adjacent independent increments with unique control entry.

The two-instruction effect is identical for all register values; no other
guarded edge may enter the second member. Counts are not runtime proofs.
"""
from pathlib import Path
import sys,json,itertools,collections
import os
HERE=Path(__file__).resolve().parent
ROOT=Path(os.environ.get('ROOT_RESEARCH_WORKSPACE', HERE/'generated')).resolve()
(ROOT/'root_work').mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(HERE.parent/'encoding'))
import encoding_support as q
import recompile219 as c
s,b=q.s,q.b
BASE=q.W/'K219_Construction_2026-10-20'
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
S=json.loads((BASE/'machine/sites219.json').read_text());old=s.tree(S)
G=s.graph_intervals(S);pred=collections.defaultdict(set)
for i,(_,targets)in enumerate(G):
 for j in targets:pred[j].add(i)
groups=collections.defaultdict(list)
for i,(a,bb)in enumerate(zip(S,S[1:])):
 if a[1]==bb[1]=='CI'and a[2]!=bb[2]and pred[i+1]=={i}:
  groups[a[2],bb[2]].append(i)
print('GROUPS',dict(groups),flush=True)
assert not any(i+1 in sum(groups.values(),[])for i in sum(groups.values(),[]))
out=ROOT/'root_work/increment_commute219';out.mkdir(exist_ok=True);records=[]
for bits in itertools.product([0,1],repeat=len(groups)):
 if not any(bits):continue
 rows=[r.copy()for r in S];changes=[]
 for bit,(regs,ordinals)in zip(bits,groups.items()):
  if not bit:continue
  for i in ordinals:rows[i][2],rows[i+1][2]=rows[i+1][2],rows[i][2];changes.append(i)
 new=s.tree(rows);gg=s.graph_intervals(rows)
 assert [r[1]for r in gg]==[r[1]for r in G]
 assert s.graph_arithmetic(rows)[0]==gg
 rec={'bits':bits,'increment_pairs':changes,'metrics':s.metrics(new)}
 try:U,m=c.compile_tree(T,old,new,extend_direct=True);rec['compiler']=m
 except Exception as exc:rec['error']=repr(exc);U=None
 if rec.get('compiler',{}).get('working_states',999)<=219:
  d=out/''.join(map(str,bits));d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rows));(d/'candidate.tm').write_bytes(b.table_bytes(U));(d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
 records.append(rec);print(json.dumps(rec),flush=True)
(out/'summary.json').write_text(json.dumps({'groups':[[list(k),v]for k,v in groups.items()],'records':records},indent=2)+'\n')
