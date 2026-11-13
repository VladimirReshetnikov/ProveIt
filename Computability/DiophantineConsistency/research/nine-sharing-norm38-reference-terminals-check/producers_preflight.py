#!/usr/bin/env python3
"""Point-in-time recheck of both multi-stage reference producers; no Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];I=D/'research/nine-sharing-norm38-reference-initial-split-check/attempt01';G=D/'research/nine-sharing-norm38-reference-gates-batched-check/attempt01';IT=Path('/tmp/nine-sharing-norm38-reference-initial-split-check-20261105');GT=Path('/tmp/nine-sharing-norm38-reference-gates-batched-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
need(sha(I/'state.json')==sha(IT/'state.json')=='ca49ec6fa785a5ad3eff917d313e83db38464cff16209a646115a8e19cc89d55','initial state');need(sha(G/'state.json')==sha(GT/'state.json')=='87e43d4d8be3fec16e9fb8fd0b2d28927dc3795d92c2e727491ab15f1a0c9835','gates state');guards=0;total=0
for tag,temp,packet,count in [('initial',IT,I,8),('gates',GT,G,13)]:
 s=json.loads((packet/'state.json').read_text());need(s['status']=='PASS' and len(s['rows'])==count,'status '+tag);prior={}
 for row in s['rows']:
  n=row['module'];total+=1;need(all(row[k]['exit']==0 and row[k]['stop_reason'] is None and not row[k]['monitor_errors'] and not row[k]['observed_descendant_pids'] for k in ('deps','compile')),'exit '+n);need(sha(temp/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(temp/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'source/object '+n)
  for k in ('deps','compile'):need(sha(temp/(n+'-'+k+'.txt'))==sha(packet/(n+'-'+k+'.txt'))==row[k]['log_sha256'],'log '+n+k)
  for mod,dep in row['dependencies'].items():
   q=Path(dep['path']);need(q.is_file() and str(q.resolve())==dep['realpath'] and sha(q)==dep['sha256'],'dependency '+mod);short=mod.split('.')[-1]
   if short in prior:need(dep['sha256']==prior[short] and q==temp/'lib/DiophantineConsistency'/(short+'.olean'),'local route '+mod)
  for path,v in row['direct_guard'].items():
   guards+=1;q=Path(path)
   if v is None:need(not os.path.lexists(q),'unexpected '+path)
   else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+path)
  prior[n]=row['object_sha256']
 for path,target in s['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
 if tag=='initial':need(prior['Norm38ReferenceInitialAll']=='be80de6feaa282e9b1fa15a265474cecd4f1b20e50d846d78faa049fcbd0a100','initial object')
 else:need(prior['Norm38ReferenceGatesAll']=='a2ed1f5582804d525fab3ec9bd5fa3346fcfad3036fcdedce8e4654ed4dce7dd','gates object')
 if tag=='gates':
  for n in prior:need(not os.path.lexists(IT/'lib/DiophantineConsistency'/(n+'.olean')),'initial overlay collision '+n)
need(not os.path.lexists(IT/'lib/DiophantineConsistency/Norm38ReferenceTerminals.olean'),'target shadow')
print(json.dumps({'status':'PASS_REFERENCE_PRODUCER_SURVEY','initial_rows':8,'gate_rows':13,'guard_slots':guards,'initial_outer_exit':'not captured','scope':'Recorded producer and selected overlay point checks; no Lean or complete transitive/dynamic ancestry.'},sort_keys=True,indent=2))
