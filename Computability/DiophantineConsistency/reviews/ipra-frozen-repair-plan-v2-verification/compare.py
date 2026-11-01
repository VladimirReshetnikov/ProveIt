#!/usr/bin/env python3
"""Compare independent physical-origin fixed-point plans, not Lean proofs."""
from pathlib import Path
import hashlib,json,shutil
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';A=V/'ipra-frozen-repair-plan-v2';B=V/'ipra-frozen-repair-plan-v2-independent';F=V/'ipra-adaptive-native-fixed-continuation/manifest.json';LOGA=Path('/tmp/ipra-frozen-repair-origin-v2-author.log');LOGB=Path('/tmp/ipra-frozen-repair-origin-v2-independent.log');h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 b=Path(p).read_bytes();return json.loads(b),hashlib.sha256(b).hexdigest()
a,ah=read(A/'manifest.json');b,bh=read(B/'manifest.json');ch=h(__file__);fh=h(F);assert a['fixed_manifest_sha256']==b['fixed_manifest_sha256']==fh
pa=(A/'prepare.py').read_text();pb=(B/'prepare.py').read_text();assert pa.replace("OUT=V/'ipra-frozen-repair-plan-v2'","OUT=V/'ipra-frozen-repair-plan-v2-independent'")==pb
assert h(A/'prepare.py')==a['origin_preparer_sha256'] and h(B/'prepare.py')==b['origin_preparer_sha256'];assert h(A/'replay.py')==a['driver_sha256']==h(B/'replay.py')==b['driver_sha256']
keys=['author_state_path','author_state_sha256','peer_state_path','peer_state_sha256','fixed_manifest_sha256','source_sha256','parent_inventory','direct_imports','external_files','external_absent','external_direct_paths','external_resolved_paths','external_absent_paths','external_lookup','lean_sha256','driver_sha256','known_seeds','unknown_or_mismatched_origins','origin_nodes','reachable_source_count','source_graph_sha256','boundary']
for k in keys:assert a[k]==b[k],k
assert len(a['order'])==len(b['order']) and set(a['order'])==set(b['order']);assert set(a['order'])==set(a['direct_imports'])==set(b['direct_imports'])
for m in [a,b]:
 done=set();dirty=set(m['order'])
 for n in m['order']:
  assert all(d not in dirty or d in done for d in m['direct_imports'][n]),n
  done.add(n)
 assert m['order'][-1]=='DiophantineConsistency.IPRAAdaptiveNativeZFCChecks'
def without_own(m,p):
 skip={str((p/'prepare.py').resolve()),str((p/'replay.py').resolve())};return {k:v for k,v in m['origin_guard'].items() if k not in skip}
ga=without_own(a,A);gb=without_own(b,B);assert ga==gb
assert a['origin_guard'][str((A/'prepare.py').resolve())]==h(A/'prepare.py') and b['origin_guard'][str((B/'prepare.py').resolve())]==h(B/'prepare.py')
assert a['origin_guard'][str((A/'replay.py').resolve())]==a['driver_sha256'] and b['origin_guard'][str((B/'replay.py').resolve())]==b['driver_sha256']
assert 'PASS-plan' in LOGA.read_text() and 'PASS-plan' in LOGB.read_text();la=h(LOGA);lb=h(LOGB)
def audit():
 assert h(__file__)==ch and h(A/'manifest.json')==ah and h(B/'manifest.json')==bh and h(F)==fh and h(LOGA)==la and h(LOGB)==lb
 assert all(h(p)==v for p,v in ga.items())
 assert h(A/'prepare.py')==a['origin_preparer_sha256'] and h(B/'prepare.py')==b['origin_preparer_sha256'] and h(A/'replay.py')==a['driver_sha256'] and h(B/'replay.py')==b['driver_sha256']
audit();shutil.copyfile(LOGA,D/'author.log');shutil.copyfile(LOGB,D/'independent.log');assert h(D/'author.log')==la and h(D/'independent.log')==lb;audit()
receipt={'status':'MATCHED_PLAN','author_manifest_sha256':ah,'independent_manifest_sha256':bh,'author_preparer_sha256':a['origin_preparer_sha256'],'independent_preparer_sha256':b['origin_preparer_sha256'],'replay_sha256':a['driver_sha256'],'compare_sha256':ch,'dirty_count':len(a['order']),'dirty_modules':sorted(a['order']),'unknown_origins':a['unknown_or_mismatched_origins'],'origin_node_count':len(a['origin_nodes']),'common_origin_guard_count':len(ga),'author_log_sha256':la,'independent_log_sha256':lb,'boundary':a['boundary']+' This is a matched provenance plan, not a Lean proof.'}
(D/'receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');print('MATCHED_PLAN',len(a['order']),'dirty',len(a['origin_nodes']),'nodes',len(ga),'guarded files',flush=True)
