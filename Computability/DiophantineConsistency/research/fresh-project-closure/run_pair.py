#!/usr/bin/env python3
"""Run two fresh builders sequentially and record process exits and matched receipt."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
from compare import compare
D=Path(__file__).resolve().parent;H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--snapshot',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--provider-receipt',type=Path,required=True);p.add_argument('--snapshot-sha256',required=True);p.add_argument('--provider-sha256',required=True);p.add_argument('--foundation-input',type=Path,required=True);p.add_argument('--expected-axiom-reports',type=int,required=True);a=p.parse_args()
out=a.output.absolute();out.mkdir(parents=True,exist_ok=False);state={'status':'RUNNING','runs':[],'snapshot_sha256':a.snapshot_sha256,'provider_sha256':a.provider_sha256,'driver_sha256':H(D/'rebuild.py'),'comparator_sha256':H(D/'compare.py'),'coordinator_sha256':H(Path(__file__))}
def save():
 q=out/'pair-state.tmp';q.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');q.replace(out/'pair-state.json')
save()
try:
 for label in ('author','peer'):
  log=out/(label+'-process.log');folder=out/label
  cmd=[sys.executable,str(D/'rebuild.py'),'--snapshot',str(a.snapshot),'--output',str(folder),'--provider-receipt',str(a.provider_receipt),'--snapshot-sha256',a.snapshot_sha256,'--provider-sha256',a.provider_sha256,'--foundation-input',str(a.foundation_input),'--expected-axiom-reports',str(a.expected_axiom_reports)]
  with log.open('x') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
  item={'label':label,'exit':r.returncode,'process_log':str(log),'process_log_sha256':H(log),'builder_state_sha256':H(folder/'state.json') if (folder/'state.json').is_file() else None};state['runs'].append(item);save()
  if r.returncode:raise RuntimeError(('builder failed',label,r.returncode))
  print(label,'exit',r.returncode,flush=True)
 result=compare(out/'author/state.json',out/'peer/state.json')
 for item in state['runs']:
  if H(item['process_log'])!=item['process_log_sha256'] or H(out/item['label']/'state.json')!=item['builder_state_sha256']:raise RuntimeError(('process log or builder state changed',item['label']))
 if H(D/'rebuild.py')!=state['driver_sha256'] or H(D/'compare.py')!=state['comparator_sha256'] or H(Path(__file__))!=state['coordinator_sha256']:raise RuntimeError('driver changed during replay')
 state.update(status='MATCHED_PASS',comparison=result);save();print('MATCHED_PASS',result['rows'],'rows',flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
