#!/usr/bin/env python3
"""HELD: one no-clobber 1-stage runner invocation with actual exit capture."""
from pathlib import Path
from hashlib import sha256
import argparse,json,os,re,subprocess,sys,time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;RUN=H/'run.py';PREFLIGHT=H/'observations/preflight-attempt01/terminal.json';POLICY=H/'observations/policy-attempt01/result.json'
PINS={RUN:'b6bfa68996e1263d3e42c924e0b78a538fd5d4a9f94719535410cea57266cb42',PREFLIGHT:'7c4c888dfebd36d9b3bbbf363414e0a2736063c84ddeeff1a25959a53206443b',POLICY:'469b46eb7490e8184cf9c035f4016dae57854fce7e6efd2a8884c5bc820aa7aa'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
parser=argparse.ArgumentParser();parser.add_argument('--attempt',required=True);args=parser.parse_args()
if re.fullmatch(r'attempt[0-9]{2,}',args.attempt) is None:raise SystemExit('bad attempt')
if any(re.fullmatch(r'[0-9a-f]{64}',h) is None for h in PINS.values()):raise SystemExit('held: final runner, preflight and policy must be pinned')
O=H/'observations'/('outer-'+args.attempt);child=H/'observations'/args.attempt
if os.path.lexists(O) or os.path.lexists(child):raise SystemExit('attempt exists')
for p,h in PINS.items():
 if sha(p)!=h:raise SystemExit('input drift '+str(p))
wrapper_before=sha(__file__);O.mkdir(parents=True);cmd=[sys.executable,'-I','-S','-B',str(RUN),'--attempt',args.attempt];env={'PATH':'/usr/bin:/bin'};start=time.time_ns()
with (O/'stdout').open('x') as out,(O/'stderr').open('x') as err:
 proc=subprocess.Popen(cmd,stdout=out,stderr=err,env=env);(O/'pid').write_text(str(proc.pid)+'\n');code=proc.wait()
child_result=child/'result.json';child_status=None
if child_result.is_file():
 try:child_status=json.loads(child_result.read_text()).get('status')
 except (OSError,ValueError,AttributeError):child_status=None
r={'command':cmd,'env':env,'exit':code,'start_ns':start,'end_ns':time.time_ns(),'inputs_before':{str(p):h for p,h in PINS.items()},'inputs_after':{str(p):sha(p) for p in PINS},'wrapper_sha256_before':wrapper_before,'wrapper_sha256_after':sha(__file__),'stdout_sha256':sha(O/'stdout'),'stderr_sha256':sha(O/'stderr'),'child_result_sha256':sha(child_result) if child_result.is_file() else None,'child_status':child_status}
tmp=O/'terminal.tmp';tmp.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');os.replace(tmp,O/'terminal.json')
print(json.dumps({'exit':code,'inputs_stable':r['inputs_before']==r['inputs_after'],'wrapper_stable':r['wrapper_sha256_before']==r['wrapper_sha256_after'],'terminal_sha256':sha(O/'terminal.json')}))
if code or child_status!='PASS' or r['inputs_before']!=r['inputs_after'] or r['wrapper_sha256_before']!=r['wrapper_sha256_after']:raise SystemExit(1)
