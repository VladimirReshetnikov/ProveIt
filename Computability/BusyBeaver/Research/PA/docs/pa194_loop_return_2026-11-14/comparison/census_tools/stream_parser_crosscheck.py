#!/usr/bin/env python3
"""Differentially check bounded-retention traversal against the supplied full-tree traversal."""
from pathlib import Path
import hashlib,json,sys
import json_inventory as js
import stream_json_tables as streaming
import literal_inventory as lit
HERE=Path(__file__).resolve().parent

def signature(tm):return hashlib.sha256(repr(tuple(sorted(tm[0].items()))).encode()).hexdigest()
def ordinary(data):
 stack=[('$',json.loads(data))];found=[]
 while stack:
  p,x=stack.pop();tm=js.decode(x)
  if tm:
   if len(tm[1])>=2:found.append((p,signature(tm)))
   continue
  if isinstance(x,dict):stack.extend((p+'/'+str(k),v) for k,v in x.items() if isinstance(v,(dict,list,str)))
  elif isinstance(x,list):stack.extend((p+'/'+str(i),v) for i,v in enumerate(x) if isinstance(v,(dict,list,str)))
 return sorted(found)
def check(data,name):
 expected=ordinary(data);actual=[]
 streaming.scan(data,lambda p,tm:actual.append((p,signature(tm))))
 if expected!=sorted(actual):raise ValueError(name+' traversal mismatch')
 return {'name':name,'bytes':len(data),'recognized_table_occurrences':len(expected),'equal':True}

def main():
 p=HERE.parent/'candidates/PA194LCG.tm';tm=lit.parse_table(p.read_bytes());rows,states,halt=tm;assert states==set(range(194))
 pairs=[[list(rows[q,b]) for b in (0,1)] for q in range(194)]
 records=[{'state':q,'read':b,'write':w,'direction':d,'next':t,'irrelevant':'data'} for (q,b),(w,d,t) in sorted(rows.items())]
 obj={'padding':'x'*6_000_000,'row_arrays':[[q,b,w,d,t] for (q,b),(w,d,t) in sorted(rows.items())],'paired_actions':pairs,'flat_actions':[a for pair in pairs for a in pair],'state_dictionary':{str(q):pairs[q] for q in range(194)},'transition_keys':{f'({q},{b})':list(a) for (q,b),a in rows.items()},'records':records,'embedded_text':p.read_text(),'signed_moves':[[q,b,w,(-1 if d=='L' else 1),t] for (q,b),(w,d,t) in sorted(rows.items())]}
 receipts=[check(json.dumps(obj).encode(),'all-eight-encodings-under-large-wrapper')]
 if len(sys.argv)>1:
  repo=Path(sys.argv[1])
  for name in ('pa194_tdy_2026-11-14/comparison/corpus_tables.json','pa194nq_research_2026-11-13/comparison/current_census.json'):
   fp=repo/'Computability/BusyBeaver/Research/PA/docs'/name;receipts.append(check(fp.read_bytes(),name))
 result={'ok':True,'method':'Exact (JSON pointer, normalized rows) agreement between full-tree and bounded-retention traversals. Shared table-shape validator is inherited.','cases':receipts}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
