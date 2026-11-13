#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-first-cut-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-first-cut-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'67aaa33d6d65abc688af58a9bbca10288015a1223a9f6dc571b5fa1524ee1ed8','Sign33FirstCut-compile.txt':'17d3bdf864c4d7a4d56cff7d2e8d958b035b2feb22aecdd9e2c86030c860bb26','outer-observation.json':'db81acb44753e1bee75557c1055ad3ee6f16c3cbfb49710c508df7514aa93f21'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(98588,1)
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33FirstCut' and 'object_sha256' not in r and not (out/'lib/DiophantineConsistency/Sign33FirstCut.olean').exists()
assert r['source_sha256']=='b522f8e9869714e04be8eb69eef93668b6aa6ee65f6f0e974ce8bdfb2eba5c74' and h(p/'src/DiophantineConsistency/Sign33FirstCut.lean')==r['source_sha256']
assert r['deps']['exit']==0 and r['compile']['exit']==1 and r['compile']['stop_reason'] is None
for k in ('deps','compile'):assert not r[k]['monitor_errors'] and not r[k]['observed_descendant_pids'] and h(a/('Sign33FirstCut-'+k+'.txt'))==r[k]['log_sha256']
log=(a/'Sign33FirstCut-compile.txt').read_text();assert 'Function expected at' in log and 'List.mem_cons_self' in log and "first_residual_eval' depends on axioms: [propext, Classical.choice, Quot.sound]" in log and 'sorryAx' in log
dep=r['dependencies']['DiophantineConsistency.SharingSign33Squares'];assert dep['sha256']=='48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1173
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':98588,'direct_guard_slots':100,'overlay_links':1173,'scope':'failed module, no Lean replay or successful object'},sort_keys=True,indent=2))
