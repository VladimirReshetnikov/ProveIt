#!/usr/bin/env python3
"""Root-owned serial driver of the reviewed per-unit guard; stop at any failure."""
from pathlib import Path
import subprocess,json,hashlib
ROOT=Path('/tmp/zfc-rotation244-runtime-ports-v1')
CONTROL=ROOT/'control'
GUARD=CONTROL/'check_runtime.py'
MANIFEST=CONTROL/'runtime-manifest.json'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(GUARD)=='0c9cc3527dc255c8e23ffc543067e230c05365007dcda71266fa0f3daba28ee8'
assert sha(MANIFEST)=='28c577e87e4c51d5740cfea2720c8a2ea41ff6777bc73eabca14bf955cdff438'
m=json.loads(MANIFEST.read_text()); log=CONTROL/'root-execution';log.mkdir(exist_ok=False)
results=[]
for name in ['mark','boxes','symbolic','site','frame','instruction','runtime']:
 u=m['units'][name];args=['python3','-B',str(GUARD),'--unit',name]
 for parent in u['future_parents']:
  record=ROOT/parent/'run1/verification.json';d=json.loads(record.read_text())
  assert d['status']=='PASS' and d['warnings']==0
  args+=['--parent',parent,str(record),sha(record)]
 for phase in ['prepared1','run1']:
  dest=ROOT/name/phase;assert not dest.exists(),dest
  cmd=args+(['--prepare-only'] if phase=='prepared1' else [])+['--output',str(dest)]
  r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  (log/(name+'-'+phase+'.log')).write_text(r.stdout)
  assert r.returncode==0,(name,phase,r.stdout)
  actual=dest/'verification.json';data=json.loads(actual.read_text())
  assert data['status']==('PREPARED_NOT_BUILT' if phase=='prepared1' else 'PASS')
  if phase=='run1':
   assert data['warnings']==0
   summary=dict(unit=name,record=str(actual),sha256=sha(actual),probes=data['named_axiom_probes'],callers=data['callers'],warnings=data['warnings'],seconds=sum(c['seconds']for c in data['commands']))
   results.append(summary);(log/'results.json').write_text(json.dumps(results,indent=2)+'\n')
   print(json.dumps(summary),flush=True)
print('ALL_SEVEN_PASS',flush=True)
