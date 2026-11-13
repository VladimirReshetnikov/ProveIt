#!/usr/bin/env python3
"""Read-only structured check of seven candidate source/session observations."""
from hashlib import sha256
from pathlib import Path
from collections import Counter
import json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
INPUT=D/'research/trace75-graph-support-28-triage/observations/attempt01/stdout'
FINAL=D/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json'
PINS={INPUT:'a1f701226ce2c5c1f9eef7b627f4d6ce6aa494bc4689c846d8617f172d750570',
      FINAL:'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c'}
def need(b,m):
    if not b:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PINS.items():need(sha(p)==h,'input drift '+str(p))
triage=json.loads(INPUT.read_text());final=json.loads(FINAL.read_text());need(triage['status']=='PASS' and final['status']=='PASS','input status')
records=[];counts=Counter();observed={}
def remember(p):
    h=sha(p);observed[str(p)]=h;return h
for row in triage['records']:
    candidates=row['local_observation_json_dual_hash_candidates']
    if not candidates:continue
    n=row['module'];short=n.split('.')[-1];need(len(candidates)==1,'ambiguous observation '+n)
    c=candidates[0];p=Path(c['path']);need(p.is_file() and remember(p)==c['sha256'],'observation drift '+n)
    q=json.loads(p.read_text());sh=row['overlay_source']['sha256'];oh=row['selected_olean_sha256']
    need(q['direct_object_sha256'][short]==oh,'object hash table mismatch '+n)
    runs=[r for r in q['runs'] if r.get('source_sha256')==sh and r.get('exit')==0]
    need(len(runs)==1 and isinstance(runs[0].get('session'),int),'successful source session ambiguous '+n)
    run=runs[0];root=p.parents[1];source=(root/run['source']).resolve();log=(root/run['log']).resolve()
    need(source.is_relative_to(root) and log.is_relative_to(root),'observation path escapes '+n)
    need(source.is_file() and remember(source)==sh and log.is_file() and remember(log)==run['log_sha256'],'session source/log drift '+n)
    selected=final['selected_project'][n]['.olean'];out=Path(q['overlay'])/(n.replace('.','/')+'.olean')
    need(out.is_file() and remember(out)==oh and selected['sha256']==oh,'observed overlay object drift '+n)
    final_path=Path(selected['path']);need(final_path.is_file() and remember(final_path)==oh and str(final_path.resolve())==selected['resolved'],'final selection drift '+n)
    same=out.resolve()==final_path.resolve();counts['same_live_realpath' if same else 'different_live_realpath']+=1
    records.append({'module':n,'observation':str(p),'observation_sha256':c['sha256'],'reported_session':run['session'],
     'reported_source':str(source),'source_sha256':sh,'reported_log':str(log),'log_sha256':run['log_sha256'],
     'reported_overlay_object':str(out),'reported_overlay_realpath':str(out.resolve()),'final_realpath':str(final_path.resolve()),
     'same_live_realpath':same,'object_sha256':oh})
need(len(records)==7,'candidate count changed')
for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
for p,h in observed.items():need(Path(p).is_file() and sha(p)==h,'observed artifact changed '+p)
print(json.dumps({'status':'PASS','summary':dict(counts),'records':records,
 'scope':'reported successful source session and separately recorded object hash; no atomic session-output linkage, producer-time direct imports, or Lean replay'},sort_keys=True))
