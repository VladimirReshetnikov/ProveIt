#!/usr/bin/env python3
"""Read-only audit captured BFS selected headers, objects, companion overlap and stage receipts."""
from pathlib import Path
from collections import deque
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'direct-bfs-80-model-halt-serialized-audit/observations/attempt01/result.json';RE=R/'direct-bfs-80-model-halt-serialized-audit/observations/reconcile01.json';OLD=R/'ordinary12-direct90-ipra-join/observations/attempt03/result.json';RT=R/'direct-bfs-80-model-halt-prototype/observations/directbfs80modelhalt-attempt03/terminal.json';S=R/'direct-bfs-80-model-halt-prototype/DirectBFS80ModelHalt.lean';RUN=R/'direct-bfs-80-model-halt-prototype/run-v3.py'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
a=j(P);recon=j(RE);old=j(OLD)['post_headers']['project'];t=j(RT)
assert sha(P)=='9591ab25369f57a711315fbee02bd19a360ec4aba15535dc44e85cc983a84003' and sha(RE)=='ae5feb55ac464e4937d109bcdb5d0a5369ba400b1f752566f18f5a194e04c304' and a['status']=='PASS_CAPTURE'
assert sha(RT)==a['root_receipt_sha256'] and t['exit']==0 and t['reason'] is None and t['pins']==t['after'] and t['direct_imports']==t['direct_imports_after']
assert sha(S)==sha(RT.parent/'source.txt')==t['pins']['source'] and sha(RUN)==t['pins']['runner'] and sha(Path(t['output_root'])/'DirectBFS80ModelHalt.olean')==t['object_sha256']==a['root_object_sha256']=='583dd7aa369634a3e575b6fd38f774ead915a751d7fce7bd8e5a64d620dfbf30'
assert not re.search(r'\b(?:sorry|admit)\b',S.read_text());logs=(RT.parent/'stdout').read_text()+(RT.parent/'stderr').read_text();assert sha(RT.parent/'stdout')==t['stdout_sha256'] and sha(RT.parent/'stderr')==t['stderr_sha256']
assert "'DirectBFS80ModelHalt.graph_halts' depends on axioms: [propext, Classical.choice, Quot.sound]" in logs and not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',logs)
cl=a['closure'];proj=cl['project'];outside=cl['outside'];assert len(proj)==739 and len(outside)==43 and not a['overlaps'] and not a['conflicting_overlaps']
todo=deque(cl['roots']);visited=set();leaves=set()
while todo:
 n=todo.popleft()
 if n in visited or n in leaves:continue
 if n not in proj:leaves.add(n);continue
 visited.add(n);todo.extend(proj[n]['imports'])
assert visited==set(proj) and leaves==set(outside)
roots=[Path(t['output_root'])]+[Path(x) for x in t['lean_path'].split(':')]+[Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
for group in (proj,outside):
 for name,row in group.items():
  p=Path(row['path']);assert p.is_file() and sha(p)==row['record']['sha256'] and str(p.resolve())==row['record']['resolved']
  rel=Path(name.replace('.','/')+'.olean');selected=next((root/rel for root in roots if (root/rel).is_file()),None)
  assert selected is not None and selected.resolve()==p.resolve()
  stem=str(p)[:-6]
  for ext,record in row['companions'].items():
   f=Path(stem+ext);assert f.is_file()==(record is not None)
   if record is not None:assert sha(f)==record['sha256'] and str(f.resolve())==record['resolved']
for x in t['direct_imports']:
 row=proj.get(x['module'],outside.get(x['module']));assert row is not None and x['sha256']==row['record']['sha256'] and Path(x['path']).resolve()==Path(row['path']).resolve()
matched=[];diff=[];absent=[]
for n,row in proj.items():
 if n not in old:absent.append(n);continue
 prev=old[n];dig=lambda a:None if a is None else a['sha256']
 eq=dig(row['record'])==dig(prev['record']) and all(dig(row['companions'][k])==dig(prev['companions'][k]) for k in row['companions'])
 (matched if eq else diff).append(n)
assert len(matched)==529 and not diff and len(absent)==210 and sorted(matched)==recon['matched'] and sorted(absent)==recon['absent_from_prior']
for x in recon['chunks']:
 rt=Path(x['receipt']);z=j(rt);assert sha(rt)==x['receipt_sha256'] and z['object_sha256']==x['object_sha256']==proj[x['module']]['record']['sha256']
assert len(recon['chunks'])==59
assert len(a['producer_direct'])==137 and not a['producer_direct_mismatches']
receipts=0;comparisons=0
for name,items in a['producer_direct'].items():
 for rec in items:
  p=Path(rec['receipt']);assert sha(p)==rec['receipt_sha256'];source=j(p);receipts+=1
  for z in rec['direct_imports_compared']:
   dep=z['module'];row=proj.get(dep,outside.get(dep));assert row and z['producer_sha256']==z['selected_sha256']==row['record']['sha256'] and z['matches']
   assert any(i['module']==dep and i['sha256']==z['producer_sha256'] for i in source['direct_imports']);comparisons+=1
print('PASS selected captured graph',len(proj),'project',len(outside),'outside; captured import reachability, current object and companion hashes')
print('prior object+companion overlaps',len(matched),'differing',len(diff),'absent',len(absent),'chunk receipts',len(recon['chunks']))
print('producer modules',len(a['producer_direct']),'receipt files',receipts,'recorded comparisons',comparisons)
print('root source',sha(S),'root object',t['object_sha256'],'receipt',sha(RT))
print('No Lean/header reread, complete historical producer-time or external package-transitive provenance claim')
