#!/usr/bin/env python3
"""Audit terminated v5 attempt and exact historical warning evidence; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-coherent-rebuild';O=P/'observations/attempt03';OUT=P/'observations/outer-attempt03';PLAN=D/'reviews/ten-positive-80-127-rebuild-preflight/observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
r=j(O/'result.json');outer=j(OUT/'terminal.json');plan=j(PLAN);stages=r['stages'];assert r['status']=='FAILED' and len(stages)==13 and outer['exit']==1
assert sha(P/'run-v5.py')==outer['runner_sha256_before']==outer['runner_sha256_after']=='67f287a75d095fc45abde2d14acc732110956e3e248c154e817f92b14eb43558'
assert sha(OUT/'stdout')==outer['stdout_sha256'] and sha(OUT/'stderr')==outer['stderr_sha256'] and 'diagnostic or sorryAx DiophantineConsistency.ModelRatioBounds' in (OUT/'stderr').read_text()
for path,digest in r['inputs'].items():assert sha(path)==digest
assert sha(O/'initial-project.json')==r['initial_project_sha256'] and sha(O/'outside-baseline.json')==r['outside_baseline_sha256'] and [x['module'] for x in stages]==plan['ordered'][:13]
bases={3:('nine-variable-ipra-stages-6-9-author-observation','008','1848875f336080bc59033d40b66a69d97cc9d1e90904d4f0d559b998fff7de92'),5:('nine-variable-ipra-stages-3-5-author-audit','004','6af6ec8ca3ec1f14663f214b53f728a9a88b7b415ea8e68b769b27b197e44f0d'),13:('nine-variable-ipra-stages-6-9-author-observation','006','442a964429a3898a6110137b53268c9b370c60bb7de38899565d2885dd865c1b')}
for i,x in enumerate(stages,1):
 assert x['index']==i and x['exit']==0 and x['reason'] is None and x['direct_before']==x['direct_after']
 a=O/f'stage-{i:03d}.stdout';b=O/f'stage-{i:03d}.stderr';assert sha(a)==x['stdout_sha256'] and sha(b)==x['stderr_sha256']
 src=next(Path(z) for z in x['command'] if z.endswith('.lean'));assert sha(src)==x['source_sha256']==plan['sources'][x['module']]['sha256']
 assert x['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and x['preflight']['mem_available_kib']>=8*1024**2 and len(x['preflight']['lean'])<2
 assert all(s['mem_available_kib']>=8*1024**2 and len(s['lean'])<=2 for s in x['samples'])
 for dep,parts in x['direct_after'].items():
  for rec in parts.values():
   if rec is not None:assert sha(rec['path'])==rec['sha256'] and str(Path(rec['path']).resolve())==rec['resolved']
 text=a.read_text()+b.read_text()
 if i in bases:
  folder,num,digest=bases[i];root=D/'reviews'/folder/'author';f=root/'receipts'/(num+'.json');base=root/'warning-policies'/(num+'.log');hist=j(f)
  assert hist['status']=='PASS' and hist['module']==x['module'] and hist['source_sha256']==x['source_sha256'] and hist['warning_policy']['baseline_sha256']==sha(base)==digest
  assert text.replace(str(src),'<SOURCE>')==base.read_text() and text.count('warning:')==hist['warning_policy']['warning_count']==(4 if i==13 else 3)
  if i<13:assert x['warning_exception']['baseline_sha256']==digest and x['warning_exception']['receipt_sha256']==sha(f)
  else:assert 'warning_exception' not in x and 'output' not in x
  print('stage',i,x['module'],'exact normalized historical baseline',digest)
 else:assert not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',text)
 if i<13:
  obj=x['output']['.olean'];assert sha(obj['path'])==obj['sha256'];print('stage',i,'object',obj['sha256'])
assert not (O/'stage-014.stdout').exists() and not (O/'stage-014.stderr').exists()
e=P/'warning-baseline-ratiobounds/observation.json';v=j(e);assert sha(e)=='059f82157cc84a1757393cef77416af7740686b80e4c1508477f7968fb7d3e9b' and v['status']=='MATCH_EXACT_NORMALIZED' and v['observed_stdout_sha256']==stages[12]['stdout_sha256'] and v['observed_stderr_sha256']==stages[12]['stderr_sha256'] and v['baseline_sha256']==bases[13][2]
print('PASS outer exit 1, 12 recorded outputs, stage 13 rejected 4-warning exact historic baseline; no stage 14 or Lean replay')
print('result',sha(O/'result.json'),'outer',sha(OUT/'terminal.json'))
