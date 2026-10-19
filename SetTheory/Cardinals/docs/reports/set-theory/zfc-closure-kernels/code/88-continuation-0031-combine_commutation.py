#!/usr/bin/env python3
"""Apply the independently reviewed q106 closed swap to a colored source.

The graph rewrite is local to physical color106. It preserves all other
physical roles and requires an independent runtime and bootstrap audit.
"""
from pathlib import Path
import argparse,json
import test_commutations as tc
s=tc.s

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--table',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 data=json.loads(a.source.read_text());memo={}
 def imp(n):
  if n not in memo:
   e=data['entries'][str(n)]
   memo[n]=s.r.mk(('N',imp(e[1]),imp(e[2]))) if e[0]=='N' else s.r.mk(tuple(e))
  return memo[n]
 root=imp(data['root'])
 roles={memo[int(n)]:q for n,q in json.loads(a.source.with_name(a.source.stem+'_roles.json').read_text())['roles'].items()}
 nr,nc,coll,proof=tc.transform(root,roles,{106});assert not coll
 T={}
 for line in a.table.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,t=line.split();T[int(q),int(b)]=int(w),d,int(t)
 for n,q in nc.items():
  if q==106:
   e=s.r.entries[n]
   assert s.r.entries[e[2]]==('CI',7) and s.r.entries[e[1]][0]=='N'
   T[106,0]=(0,'R',nc[e[1]]);T[106,1]=(1,'R',93)
 s.r.dump_graph(nr,a.output.with_suffix('.json'),dict(source_pairs=len(nc),proof=proof,collisions=coll,source_input=str(a.source),proof_status='closed independent q106 swap; binary audit separate'))
 a.output.with_name(a.output.name+'_roles.json').write_text(json.dumps({'roles':nc})+'\n')
 s.c.save_table(T,a.output.with_suffix('.tm'))
 print(dict(source_pairs=len(nc),states=len(T)//2,proof=proof,changed_rows=[106]))
if __name__=='__main__':main()
