#!/usr/bin/env python3
"""Own bounded producer reproduction. Requires the independently frozen clean peer."""
import hashlib,json,pathlib,shutil,subprocess,sys,time
O=pathlib.Path(__file__).resolve().parent
FROZEN='1626c437e96a1958f5264e2ca0bf2803c877cbdcbe37d9c789b6c168c50290d8'
PEER=pathlib.Path('/tmp/k215-upstream49-source-review/producer-review.json')
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def js(p):return json.loads(pathlib.Path(p).read_text())
def pin(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
assert sha(O/'freeze.json')==FROZEN
f=js(O/'freeze.json')
for r in f['files']:assert sha(O/r['path'])==r['sha256']
# The final independently reviewed receipt path/hash is supplied explicitly.
assert len(sys.argv)==3,'usage: run_reproduction.py PEER_JSON PEER_SHA256'
PEER=pathlib.Path(sys.argv[1]);assert sha(PEER)==sys.argv[2]
peer=js(PEER);assert 'PASS' in peer['status']
out=O/'reproduction-run1';out.mkdir(exist_ok=False)
layout=out/'layout';formal=layout/'Computability/BusyBeaver/Research/ZFC/k225-formal'
formal.mkdir(parents=True)
for p in (O/'production').rglob('*'):
 if p.is_file():q=formal/p.relative_to(O/'production');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
lean=layout/'Computability/BusyBeaver/Lean'
producer=formal/'generate_dominated_implication_lean.py'
before={'freeze':pin(O/'freeze.json'),'peer':pin(PEER),'runner':pin(pathlib.Path(__file__)),
 'owned_originals':[pin(O/r['path']) for r in f['files']],
 'disposable_inputs':[pin(p) for p in sorted(formal.rglob('*')) if p.is_file()]}
(out/'before.json').write_text(json.dumps(before,indent=2)+'\n')
jobs=[('controls',[sys.executable,'-B',str(O/'controls.py')]),
 ('generate',[sys.executable,'-B',str(producer),'--out',str(lean)]),
 ('explicit-output-check',[sys.executable,'-B',str(producer),'--out',str(lean),'--check']),
 ('explicit-default-check',[sys.executable,'-B',str(producer),'--check']),
 ('implicit-default-check',[sys.executable,'-B',str(producer)])]
records=[];status='PASS'
for number,(name,cmd) in enumerate(jobs,1):
 d=out/f'{number:02d}-{name}';d.mkdir();log=d/'stdout.log';start=time.monotonic();timed=False
 with log.open('wb') as stream:
  try:r=subprocess.run(cmd,cwd=formal,stdout=stream,stderr=subprocess.STDOUT,timeout=30);code=r.returncode
  except subprocess.TimeoutExpired:code=None;timed=True
 record={'name':name,'command':cmd,'cwd':str(formal),'timeout_seconds':30,'exit_code':code,'timed_out':timed,'seconds':time.monotonic()-start,'log':pin(log)}
 (d/'record.json').write_text(json.dumps(record,indent=2)+'\n');records.append(record)
 if code!=0 or timed:status='FAIL';break
 parsed=json.loads(log.read_text())
 if name=='controls':
  assert parsed['status']=='PASS_OWN_PRODUCER_CONTROLS'
  assert len([x for x in parsed['results'] if x['kind']=='positive'])==4
  assert len([x for x in parsed['results'] if x['kind']=='negative'])==15
 else:
  assert parsed['generic_sha256']==f['expected_core_sha256']
  assert parsed['adapter_sha256']==f['expected_adapter_sha256']
  assert parsed['raw_checked']['private_mp']==58 and parsed['checked']['private_mp']==56
  assert parsed['raw_checked']['restricted_rows']==parsed['checked']['restricted_rows']==23
  assert parsed['checked']['public_mp']==3
for r in before['owned_originals']+before['disposable_inputs']:assert sha(r['path'])==r['sha256']
assert sha(O/'freeze.json')==FROZEN and sha(PEER)==sys.argv[2]
outputs=[]
if status=='PASS':
 for name,expected in [('DominatedImplication.lean',f['expected_core_sha256']),('DomRho8.lean',f['expected_adapter_sha256'])]:
  p=lean/'BusyBeaver/ZFC'/name;assert sha(p)==expected;outputs.append(pin(p))
 assert not (formal/'dominated_implication_templates/core-prefix.txt').exists()
 assert not (formal/'dominated_implication_templates/core-suffix.txt').exists()
actual={'status':status,'jobs':records,'outputs':outputs,'all_before_input_bytes_unchanged':True,
 'source_freeze_sha256':FROZEN,'peer_sha256':sys.argv[2],'supplied_renderer_executions':0,'compiler_invocations':0,'canonical_writes':0,
 'scope':'Own producer/source diagnostic and five CLI/control invocations, no kernel or full endpoint claim.'}
(out/'actual.json').write_text(json.dumps(actual,indent=2)+'\n')
print(json.dumps({'status':status,'actual_sha256':sha(out/'actual.json'),'jobs':len(records),'output':str(out)},indent=2))
raise SystemExit(0 if status=='PASS' else 1)
