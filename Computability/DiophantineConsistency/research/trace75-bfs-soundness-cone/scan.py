#!/usr/bin/env python3
"""Compute the captured 80-to-halt graph cone above carry and fixed slots."""
from pathlib import Path
from hashlib import sha256
import json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1];P=D/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json';O=H/'observations/attempt01';PIN='ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(not O.exists() and sha(P)==PIN,'output exists or receipt drift');runner=sha(__file__);x=json.loads(P.read_text());need(x['status']=='PASS','bad BFS status');g=x['closure']['project'];root='DirectBFS80ModelHalt';todo=[root];seen=set();outside=set()
while todo:
 n=todo.pop()
 if n in seen or n in outside:continue
 if n not in g:outside.add(n);continue
 seen.add(n);todo.extend(g[n]['imports'])
seeds={'DirectBFS80Carry','Direct80FixedSlots'};need(seeds<=seen,'seed absent');affected=set(seeds)
while True:
 y=affected|{n for n in seen if set(g[n]['imports'])&affected}
 if y==affected:break
 affected=y
need(len(seen)==739 and len(affected)==21,'captured cone changed')
need(sha(P)==PIN and sha(__file__)==runner,'input drift');O.mkdir(parents=True)
r={'status':'PASS','input':str(P),'input_sha256':PIN,'runner_sha256':runner,'root':root,'seeds':sorted(seeds),'project_ancestors':sorted(seen),'outside_boundary':sorted(outside),'affected':{n:{'imports':g[n]['imports'],'object_sha256':g[n]['record']['sha256']} for n in sorted(affected)},'scope':'historical BFS80 serialized project graph only; no trace75 transfer, completeness, or file binding'}
(O/'result.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':'PASS','project':len(seen),'affected':len(affected),'sha256':sha(O/'result.json')}))
