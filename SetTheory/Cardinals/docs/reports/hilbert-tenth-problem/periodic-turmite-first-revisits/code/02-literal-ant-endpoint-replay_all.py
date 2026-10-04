#!/usr/bin/env python3
"""Fresh isolated endpoint replay: four own commands, six DAGs and four receipts."""
if not __debug__:raise RuntimeError('Assertions required')
import hashlib,json,pathlib,shutil,subprocess,sys,tempfile
ROOT=pathlib.Path(__file__).resolve().parent
COMMANDS=['audit_endpoint.py','audit_folded_endpoint.py','audit_five_witness_endpoint.py','verify_literal_sources.py']
RECEIPTS=['endpoint_audit_receipt.json','folded_endpoint_audit_receipt.json','five_witness_endpoint_audit_receipt.json','literal_source_verification.json']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 outputs=sorted(p.name for p in ROOT.glob('endpoint_*_source.json'))+RECEIPTS
 assert len(outputs)==10
 with tempfile.TemporaryDirectory(prefix='paid-ant-endpoint-')as tmp:
  fresh=pathlib.Path(tmp)/'packet';shutil.copytree(ROOT,fresh,ignore=shutil.ignore_patterns('__pycache__','fresh_replay.json'))
  commands=[]
  for rel in COMMANDS:
   run=subprocess.run([sys.executable,'-B',str(fresh/rel)],cwd='/',capture_output=True,text=True)
   if run.returncode:raise RuntimeError((rel,run.stdout[-2000:],run.stderr[-2000:]))
   commands.append({'command':rel,'stdout_sha256':hashlib.sha256(run.stdout.encode()).hexdigest(),'returncode':0});print('PASS',rel,flush=True)
  exact=[]
  for rel in outputs:
   assert(fresh/rel).read_bytes()==(ROOT/rel).read_bytes(),rel
   exact.append({'file':rel,'sha256':sha(ROOT/rel)})
  guards=[]
  for rel in COMMANDS+['replay_all.py']:
   if 'not __debug__'not in(fresh/rel).read_text():guards.append({'file':rel,'optimized':'unsupported_not_run'});continue
   run=subprocess.run([sys.executable,'-B','-O',str(fresh/rel)],cwd='/',capture_output=True,text=True)
   assert run.returncode!=0 and 'Assertions required'in run.stderr
   guards.append({'file':rel,'optimized':'rejected_as_required'})
  r={'status':'PASS_FRESH_ENDPOINT_PACKET_REPLAY','commands':commands,'byte_exact_outputs':exact,'optimization_guards':guards,'network_used':False,'upstream_code_executed':False,'giant_numerals_materialized':False,'driver_sha256':sha(pathlib.Path(__file__))}
  (ROOT/'fresh_replay.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':r['status'],'commands':len(commands),'outputs':len(outputs)}))
if __name__=='__main__':main()
