#!/usr/bin/env python3
"""Verify stopped v4 attempt and both exact historical baselines; never invoke Lean."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-coherent-rebuild';O=P/'observations/attempt02';OUT=P/'observations/outer-attempt02';PLAN=D/'reviews/ten-positive-80-127-rebuild-preflight/observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
r=j(O/'result.json');out=j(OUT/'terminal.json');plan=j(PLAN);stages=r['stages'];assert r['status']=='FAILED' and len(stages)==5 and out['exit']==1
assert out['runner_sha256_before']==out['runner_sha256_after']==sha(P/'run-v4.py')=='6065f48448b7956355ad277e481047ec88cfea7ba09d9de99fb6542513398ca9'
assert sha(OUT/'stdout')==out['stdout_sha256'] and sha(OUT/'stderr')==out['stderr_sha256'] and 'diagnostic or sorryAx DiophantineConsistency.ModelArithmetic' in (OUT/'stderr').read_text()
for path,digest in r['inputs'].items():assert sha(path)==digest
assert sha(O/'initial-project.json')==r['initial_project_sha256'] and sha(O/'outside-baseline.json')==r['outside_baseline_sha256'] and [x['module'] for x in stages]==plan['ordered'][:5]
for i,x in enumerate(stages,1):
 assert x['index']==i and x['exit']==0 and x['reason'] is None and x['direct_before']==x['direct_after']
 a=O/f'stage-{i:03d}.stdout';b=O/f'stage-{i:03d}.stderr';assert sha(a)==x['stdout_sha256'] and sha(b)==x['stderr_sha256']
 src=next(Path(z) for z in x['command'] if z.endswith('.lean'));assert sha(src)==x['source_sha256']==plan['sources'][x['module']]['sha256']
 assert x['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and x['preflight']['mem_available_kib']>=8*1024**2 and len(x['preflight']['lean'])<2
 assert all(s['mem_available_kib']>=8*1024**2 and len(s['lean'])<=2 for s in x['samples'])
 for dep,parts in x['direct_after'].items():
  for suffix,rec in parts.items():
   if rec is not None:assert sha(rec['path'])==rec['sha256'] and str(Path(rec['path']).resolve())==rec['resolved']
 text=a.read_text()+b.read_text()
 if i in (3,5):
  if i==3:
   receipt=D/'reviews/nine-variable-ipra-stages-6-9-author-observation/author/receipts/008.json';base=D/'reviews/nine-variable-ipra-stages-6-9-author-observation/author/warning-policies/008.log';expected='1848875f336080bc59033d40b66a69d97cc9d1e90904d4f0d559b998fff7de92'
   assert x['warning_exception']['baseline_sha256']==expected and x['warning_exception']['receipt_sha256']==sha(receipt)
  else:
   receipt=D/'reviews/nine-variable-ipra-stages-3-5-author-audit/author/receipts/004.json';base=D/'reviews/nine-variable-ipra-stages-3-5-author-audit/author/warning-policies/004.log';expected='6af6ec8ca3ec1f14663f214b53f728a9a88b7b415ea8e68b769b27b197e44f0d'
   assert x['module']=='DiophantineConsistency.ModelArithmetic' and 'output' not in x and 'warning_exception' not in x
  h=j(receipt);assert h['status']=='PASS' and h['module']==x['module'] and h['source_sha256']==x['source_sha256'] and h['warning_policy']['warning_count']==3 and h['warning_policy']['baseline_sha256']==sha(base)==expected
  assert text.replace(str(src),'<SOURCE>')==base.read_text() and text.count('warning:')==3
  print('stage',i,x['module'],'exact baseline',expected,'source',x['source_sha256'])
 else:assert not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',text)
 if i<5:
  obj=x['output']['.olean'];assert sha(obj['path'])==obj['sha256'];print('stage',i,'object',obj['sha256'])
assert not (O/'stage-006.stdout').exists() and not (O/'stage-006.stderr').exists()
print('PASS outer exit 1; v4 recorded exact stage-3 exception, stopped at stage 5; no stage 6, no endpoint; no Lean replay')
print('result',sha(O/'result.json'),'outer',sha(OUT/'terminal.json'))
