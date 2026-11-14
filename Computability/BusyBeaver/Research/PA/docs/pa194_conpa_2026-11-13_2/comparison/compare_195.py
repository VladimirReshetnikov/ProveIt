#!/usr/bin/env python3
"""Independent rooted action-graph census of all 195-state tables.
Starts of previous rejected tables are bound to their prior source manifest.
Every digest and every table count is recomputed; no start is guessed.
"""
from pathlib import Path
import io,json,hashlib,zipfile,argparse
from collections import defaultdict
from census_current import ROW
ROOT=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--archive-dir',type=Path,required=True);ap.add_argument('--census',type=Path,default=ROOT/'corpus/census_current.json');ap.add_argument('--out',type=Path,default=ROOT/'corpus/comparison195_replayed.json');args=ap.parse_args()
src=json.loads((ROOT/'corpus/source_manifest.json').read_text())
paths={x['name']:args.archive_dir/x['name'] for x in src}
census=json.loads(args.census.read_text())
old=ROOT/'corpus/rejected195_previous.json'
previous=json.loads(old.read_text()); starts={}
for rs in previous['classes'].values():
 for r in rs: starts[r['sha256']]=r['start']
starts['5c6afd87f7c4f24d9ad8e9e302cc21df14b6f2e3715d03322a75463a431d8455']=0
starts['061476b12943116f3228d4d3ef251c2be420dad213cef452b1ff122c9a2b0aea']=74

def member_bytes(loc):
 a,*members=loc.split('!');b=paths[a].read_bytes()
 for n in members:b=zipfile.ZipFile(io.BytesIO(b)).read(n)
 return b

def graph(b,start):
 rows={}
 for ln in b.decode().splitlines():
  m=ROW.match(ln)
  if not m:continue
  q,r,w,d,n=m.groups();rows[int(q),int(r)]=(int(w),d,int(n))
 states={q for q,r in rows}; mapping={start:0};queue=[start];result=[]
 for q in queue:
  rr=[]
  for r in(0,1):
   w,d,n=rows[q,r]
   if n not in states:nn='H'
   else:
    if n not in mapping:mapping[n]=len(mapping);queue.append(n)
    nn=mapping[n]
   rr.append([w,d,nn])
  result.append(rr)
 if len(mapping)!=195:raise ValueError(('unreachable',len(mapping)))
 canonical=json.dumps(result,separators=(',',':')).encode()
 return hashlib.sha256(canonical).hexdigest(),mapping

groups=defaultdict(list)
for t in census['tables']:
 if t['states']!=195:continue
 b=member_bytes(t['member']);digest=hashlib.sha256(b).hexdigest();assert digest==t['raw_sha256']
 start=starts[digest];g,m=graph(b,start)
 groups[g].append(dict(member=t['member'],raw_sha256=digest,start=start,terminal_labels=t['terminal_labels'],status='PA195 ordinary proof and certificates' if 'pa195_conpa_2026-11-13.zip!' in t['member'] else 'previously rejected or uncertified diagnostic'))
out={'scope':'all 195-state complete numeric tables recognized by current census; starts from supplied conventions, no inferred starts','occurrences':sum(map(len,groups.values())),'rooted_action_graph_classes':len(groups),'groups':groups}
args.out.write_text(json.dumps(out,indent=2)+'\n');print(out['occurrences'],out['rooted_action_graph_classes'])
