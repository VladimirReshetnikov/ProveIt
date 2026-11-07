#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint34-41-h-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint34-41-h-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='e9aee1f82b7bf53338fe0dadbac6bba984b2e52bfe27144963df6e2ff8e178e7' and sha(a/'outer-terminal-author-record.json')=='6e978f4a158996fedeeed4e17f9a50345ec61f15b1e965053b657d10f1e30e29';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(17198,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1253
names=['Norm38MacroHValue','Norm38MacroHPath'];objects=['3098cdaa8868fd891c7cd26649ca191cc066a00e2e802894a905d36f8e523bd1','d6f64fff7c7175db02b85101b9f4f112290cea47a6a80bb6ae1cee9344a20462'];reports=[['d33_j_value','d33_Bprime_value','d34_H_value'],['d41_H_value']];guards=[250,150]
expected=[{'Norm38MacroGprimePath':'1acfb8bf9673da2c44296cf28e642112c6018d1c25f434a420951b33352287da','Norm38MacroDependentH':'fd1691414fc25dab60414cdb181d1c92bcacffc621ee3fb19a6804008d4850ce','Norm38MacroLive18Group04':'d441a380efaacb979a20ed3370cfec35c900afd19d23eaa210b1b7d6bb76c143','Norm38MacroPrefixInputsB':'43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170'},{'Norm38MacroHValue':objects[0],'Norm38MacroCheckpoint34to41':'985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155'}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointH\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':17198,'stages':2,'guard_slots':400,'overlay_links':1253,'scope':'symbolic H at d41 with opaque rank; no Lean replay'},indent=2,sort_keys=True))
