#!/usr/bin/env python3
"""Map an associated source leaf to the old source by exact leaf-order equality."""
import argparse,json
from pathlib import Path
P=argparse.ArgumentParser();P.add_argument('grammar',type=Path);P.add_argument('path');P.add_argument('--inputs',type=Path,required=True);P.add_argument('--metadata',type=Path);P.add_argument('--output',type=Path);a=P.parse_args()
s=json.loads((a.inputs/'closed-sequence-grammar-next22.json').read_text());sym=json.loads((a.inputs/'semantic-symbols.json').read_text());l=(a.inputs/'semantic.txt').read_text().splitlines();n=int(l[0].split()[0]);names={int(q):w for k,w,q in map(str.split,l[1:n+1])};old={w:(w[:int(k)],w[int(k):])for k,w,q in map(str.split,l[1:n+1])};byast={int(v):names[int(q)]for q,v in s['sequence_ast_roots'].items()};d=json.loads(a.grammar.read_text());new={w:(l,r)for w,l,r in d['rules']}
def expand(g):
 out=[]
 def wp(w,p):
  if len(w)==1:return ep(s['atoms'][sym[w]]['ast'],p)
  for b,v in enumerate(g.get(w,old.get(w))):wp(v,p+str(b))
 def ep(i,p):
  if i in byast:return wp(byast[i],p)
  row=s['ast_dag'][i]
  if row[0]=='L':out.append((p,row[1]));return
  for b,v in enumerate(row[1:]):ep(v,p+str(b))
 ep(s['original_ast'],'');return out
older,newer=expand(old),expand(new)
assert len(older)==len(newer)==6460
assert [token for path,token in older]==[token for path,token in newer]
idx=next(i for i,(path,token)in enumerate(newer)if path==a.path);result=dict(status='EXACT_STATIC_LEAF_ORDER_MATCH',leaf_count=len(older),leaf_index=idx,old_path=older[idx][0],new_path=newer[idx][0],leaf=older[idx][1],caveat='Static syntax equality of ordered leaves under sequence association. A separate RM bisimulation certificate establishes dynamic correspondence.')
if a.metadata:
 meta=json.loads(a.metadata.read_text());result['interval_cases']=[dict(case_index=i,**m)for i,m in enumerate(meta)if m['pc']==older[idx][0]]
print(json.dumps(result,indent=2))
if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
