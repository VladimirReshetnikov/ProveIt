#!/usr/bin/env python3
"""Fresh rooted-graph comparison of all eight distinct 195-state byte tables."""
from pathlib import Path
from collections import deque,defaultdict
import argparse,json,zipfile,hashlib,re

def canonical(data,start):
 rows={}
 for line in data.decode().splitlines():
  ts=line.split()
  if len(ts)==5 and ts[0].isdigit():
   q,b,w,d,t=ts;rows[int(q),int(b)]=(int(w),d,int(t))
 states={q for q,b in rows}
 assert len(states)==195 and len(rows)==390
 ids={start:0};queue=deque([start]);out=[]
 while queue:
  q=queue.popleft();r=[]
  for b in (0,1):
   w,d,t=rows[q,b]
   if t not in states:n='HALT'
   else:
    if t not in ids:ids[t]=len(ids);queue.append(t)
    n=ids[t]
   r.append([w,d,n])
  out.append(r)
 assert len(ids)==195
 return hashlib.sha256(json.dumps(out,separators=(',',':')).encode()).hexdigest()

def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,default=Path(__file__).resolve().parent.parent/'ProveIt');args=p.parse_args()
 base=Path(__file__).resolve().parent;inv=json.loads((base/'inventory.json').read_text());groups=defaultdict(list);entries=[]
 for t in inv['tables']:
  if t['states']!=195:continue
  with zipfile.ZipFile(args.repo/'docs/incoming'/t['archive']) as z:data=z.read(t['member'])
  assert hashlib.sha256(data).hexdigest()==t['sha256']
  # These native files retain PA196's native initial control74. The two
  # unmarked native/dense pairs are also independently conjugate at74/0.
  start=74 if t['member'].endswith('.native.tm') else 0
  graph=canonical(data,start)
  entries.append({**t,'start':start,'start_inferred':False,'start_provenance':'native74 / dense0 per the six diagnostic constructions; paired aliases freshly conjugacy-checked','verified_rooted_graph_sha256':graph})
  groups[graph].append({'archive':t['archive'],'member':t['member'],'sha256':t['sha256'],'start':start})
 assert len(entries)==14 and len({t['sha256'] for t in entries})==8 and len(groups)==6
 result={'occurrences':14,'byte_strings':8,'rooted_classes':6,'all_graph_reachable_states':195,'groups':dict(groups),
         'scope':'Graph comparison only. All six are rejected diagnostic constructions; no halting or consistency conclusion follows from the census.'}
 (base/'diagnostics195.json').write_text(json.dumps(entries,indent=2)+'\n')
 (base/'diagnostics195_groups.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items()if k!='groups'},indent=2))

if __name__=='__main__':main()
