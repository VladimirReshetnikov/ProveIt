#!/usr/bin/env python3
"""Check stopped 127-stage attempt and exact historic warning baseline; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-coherent-rebuild';O=P/'observations/attempt01';OUT=P/'observations/outer-attempt01';H=D/'reviews/nine-variable-ipra-stages-6-9-author-observation/author/receipts/008.json';BASE=D/'reviews/nine-variable-ipra-stages-6-9-author-observation/author/warning-policies/008.log';PLAN=D/'reviews/ten-positive-80-127-rebuild-preflight/observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
r=j(O/'result.json');out=j(OUT/'terminal.json');historical=j(H);plan=j(PLAN);stages=r['stages'];assert r['status']=='FAILED' and len(stages)==3 and out['exit']==1
assert out['runner_sha256_before']==out['runner_sha256_after']==sha(P/'run-v3.py')=='c262d844c28fe87954cfe06d14da359d08e4d88838cb32bce025f26b072269d5'
assert sha(OUT/'stdout')==out['stdout_sha256'] and sha(OUT/'stderr')==out['stderr_sha256'] and 'diagnostic or sorryAx DiophantineConsistency.ArithmeticPellPigeonhole' in (OUT/'stderr').read_text()
for path,digest in r['inputs'].items():assert sha(path)==digest
assert sha(O/'initial-project.json')==r['initial_project_sha256'] and sha(O/'outside-baseline.json')==r['outside_baseline_sha256']
assert [x['module'] for x in stages]==plan['ordered'][:3]
for i,x in enumerate(stages,1):
 assert x['index']==i and x['exit']==0 and x['reason'] is None and x['direct_before']==x['direct_after']
 assert sha(O/f'stage-{i:03d}.stdout')==x['stdout_sha256'] and sha(O/f'stage-{i:03d}.stderr')==x['stderr_sha256']
 assert x['source_sha256']==plan['sources'][x['module']]['sha256'];src=next(Path(z) for z in x['command'] if z.endswith('.lean'));assert sha(src)==x['source_sha256']
 assert x['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and x['preflight']['mem_available_kib']>=8*1024**2 and len(x['preflight']['lean'])<2
 assert all(s['mem_available_kib']>=8*1024**2 and len(s['lean'])<=2 for s in x['samples'])
 for dep,parts in x['direct_after'].items():
  for suffix,rec in parts.items():
   if rec is not None:assert sha(rec['path'])==rec['sha256'] and str(Path(rec['path']).resolve())==rec['resolved']
 if i<3:
  logs=(O/f'stage-{i:03d}.stdout').read_text()+(O/f'stage-{i:03d}.stderr').read_text();assert not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',logs)
  obj=x['output']['.olean'];assert sha(obj['path'])==obj['sha256'];print('stage',i,x['module'],'object',obj['sha256'])
 else:
  assert 'output' not in x and x['module']=='DiophantineConsistency.ArithmeticPellPigeonhole'
  raw=(O/'stage-003.stdout').read_text()+(O/'stage-003.stderr').read_text();normalized=raw.replace(str(src),'<SOURCE>');assert normalized==BASE.read_text()
  assert sha(BASE)==historical['warning_policy']['baseline_sha256']=='1848875f336080bc59033d40b66a69d97cc9d1e90904d4f0d559b998fff7de92'
  assert historical['source_sha256']==historical['warning_policy']['source_sha256']==x['source_sha256'] and historical['warning_policy']['warning_count']==3 and normalized.count('warning:')==3
  print('stage 3 exact historical warning baseline',sha(BASE),'source',x['source_sha256'])
assert not (O/'stage-004.stdout').exists() and not (O/'stage-004.stderr').exists()
print('PASS outer exit 1; FAILED at stage 3; no stage 4 and no accepted endpoint; no Lean replay')
print('result',sha(O/'result.json'),'outer',sha(OUT/'terminal.json'))
