#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-positive-witness-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='6c5036555516687d21b39c6e5f195231b825c91bd174c49991c8087569d1e78b' and sha(p/'source-manifest.json')=='7edd6c6d98e87ec0f196fe2f782acb8a243162459a8f5ee6611d1ef085b2403c'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74Witness';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74Model'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='059edac50e1cb9c225ca4afe257b7e1ff0ddba309cb45770b9a12b920f6d6aaf' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('[ORingStructure V]','V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁','(∃ u : Fin 14 → V, (∀ i, 0 < u i) ∧ InternalZero (Sign14Positive74.expression p) u)','∃ w : Fin 14 → V, InternalZero (Sign14Optimized86Expression.expression p) w','fun i => u i - 1','tsub_add_cancel_of_le (pos_iff_one_le.mp (hu i))','(Sign14Positive74Model.zero_iff p w).mp','(internalZero_positiveShift _ w).mpr','fun i => w i + 1','(internalZero_positiveShift _ w).mp','(Sign14Positive74Model.zero_iff p w).mpr'):assert z in s
for n0 in range(20):assert n0+1>0 and (n0+1)-1==n0
for u in range(1,20):assert (u-1)+1==u
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-model-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed explicit positive-witness/model-natural zero equivalence; iPRA endpoint/file binding separate'},indent=2))
