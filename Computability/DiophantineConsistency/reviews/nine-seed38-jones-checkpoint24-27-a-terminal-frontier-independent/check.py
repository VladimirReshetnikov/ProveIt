#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint24-27-a-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint24-27-a-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='919351c779ce7eab195c669894222bf2554a16c1ae05e8d3f7b29f5572cf5738' and sha(a/'outer-terminal-author-record.json')=='1b38c12d9c5df0155b6aec0f4af3bc1cfc170b4d5e646398f81d957cb63403ff';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(12976,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1236
names=['Norm38MacroAPath','Norm38MacroAValue'];objects=['09f78d165f130d6539f85b21b612908d6c09439180937fb5ac1275fefd95f8ab','e22058fcc79740fc425fbb063007e3022a6cdc75b217385fb961a3e173dc0a31'];reports=[['lookup24_27'],['d27_A_value']];guards=[100,150]
expected=[{'Norm38MacroMValue':'aa0ba07d953598aa407e4d3c6356cc73bddd1d8b104b48440a24aad8db34695f'},{'Norm38MacroAPath':objects[0],'Norm38MacroDependentA':'ae2c004e07dd9ac2c080af9845a545e7ac46fd9418996bf3f646394a82782b12'}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointA\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 if n=='Norm38MacroAPath':assert "'DiophantineConsistency.Norm38MacroCheckpointA.path24_27' does not depend on any axioms" in log
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':12976,'stages':2,'guard_slots':250,'overlay_links':1236,'scope':'symbolic A at d27 with opaque rank; no Lean replay'},indent=2,sort_keys=True))
