#!/usr/bin/env python3
"""Independent source and provider point inspection; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];repo=D.parents[1];draft=D/'research/nine-sharing-norm38-reference-initial-split-draft';packet=D/'research/nine-sharing-norm38-reference-initial-split-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();manifest=json.loads((packet/'source-manifest.json').read_text())['rows'];assert len(manifest)==8
ref=(D/'research/nine-sharing-norm38-reference-base-retry02/src/DiophantineConsistency/Norm38ReferenceBase.lean').read_text();assignment=(D/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text();r=re.findall(r'^  let a(\d+) : R := (.+)$',ref,re.M);a=re.findall(r'^  let a(\d+) : SignedPair S := (.+)$',assignment,re.M);assert len(r)==len(a)==81
for i in range(21):
 assert int(r[i][0])==int(a[i][0])==i
 if i<14:assert r[i][1]==f'x {i}' and a[i][1]==f'⟨w {i} + 1, 0⟩'
 elif i<18:assert r[i][1]==f'p {i-14}' and a[i][1]==f'⟨ports {i-14}, 0⟩'
 else:assert r[i][1]==str((1,3,4)[i-18]) and a[i][1]==f'⟨{(1,3,4)[i-18]}, 0⟩'
 name=f'Norm38ReferenceInitialGroup{i//3:02d}';s=(draft/'src/DiophantineConsistency'/(name+'.lean')).read_text();m=re.search(r'^theorem initial_node'+f'{i:02d}'+r'\b(.*?)(?=^theorem |^end )',s,re.M|re.S);assert m
 t=m.group();assert f'assignment ports w {i}' in t and re.search(r'\) '+str(i)+r' := by',t) and 'Fin.castLE (by decide : 14 ≤ 38)' in t
alltext=(draft/'src/DiophantineConsistency/Norm38ReferenceInitialAll.lean').read_text();assert 'List.mem_map.mp hi' in alltext and 'fin_cases j' in alltext
for i in range(21):assert f'exact initial_node{i:02d} ports w' in alltext
seen=set(); names={r['module'] for r in manifest}
for row in manifest:
 for dep in row['imports']:
  if dep in names:assert dep in seen
 seen.add(row['module']);n=row['module'].split('.')[-1]+'.lean';assert sha(packet/'src/DiophantineConsistency'/n)==sha(repo/row['source'])==row['source_sha256']
base=json.loads((D/'research/nine-sharing-norm38-reference-base-retry02/attempt01/state.json').read_text());targets={row['module'].split('.')[-1]+'.olean' for row in manifest};assert not [k for k in base['overlay_links'] if Path(k).parent.name=='DiophantineConsistency' and Path(k).name in targets]
runner=packet/'run.py';p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_SOURCE_PREFLIGHT_ONLY','nodes':21,'groups':7,'stages':len(manifest),'manifest_sha256':sha(packet/'source-manifest.json'),'runner_sha256':sha(runner),'scope':'No Lean elaboration, model bridge or endpoint'},indent=2,sort_keys=True))
