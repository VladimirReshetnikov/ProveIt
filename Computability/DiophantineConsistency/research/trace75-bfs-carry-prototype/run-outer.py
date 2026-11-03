#!/usr/bin/env python3
"""HELD: one no-clobber fresh-union carry client invocation with actual exit capture."""
from pathlib import Path
from hashlib import sha256
import argparse,json,os,re,subprocess,sys,time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;RUN=H/'run.py';PREFLIGHT=H/'observations/preflight-attempt01/terminal.json';POLICY=H/'observations/policy-attempt01/result.json'
PINS={RUN:'b5f0efe4dd1f853e54a5822e77b585269910b0554511ad94c4aba170f5a7fff0',PREFLIGHT:'feeb8fa39e023e2a942ac96db8d9b02944d73e19c1f85245c879ebca4e5cd9f5',POLICY:'9788b834c2cab19a765992976bfd6d5981938015414fa20235fa12068fc85d02'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
parser=argparse.ArgumentParser();parser.add_argument('--attempt',required=True);args=parser.parse_args()
if re.fullmatch(r'attempt[0-9]{2,}',args.attempt) is None:raise SystemExit('bad attempt')
O=H/'observations'/('outer-'+args.attempt);child=H/'observations'/args.attempt
if os.path.lexists(O) or os.path.lexists(child):raise SystemExit('attempt exists')
for p,h in PINS.items():
 if sha(p)!=h:raise SystemExit('input drift '+str(p))
wrapper_before=sha(__file__);O.mkdir(parents=True);cmd=[sys.executable,'-I','-S','-B',str(RUN),'--attempt',args.attempt];env={'PATH':'/usr/bin:/bin'};start=time.time_ns()
with (O/'stdout').open('x') as out,(O/'stderr').open('x') as err:
 proc=subprocess.Popen(cmd,stdout=out,stderr=err,env=env);(O/'pid').write_text(str(proc.pid)+'\n');code=proc.wait()
r={'command':cmd,'env':env,'exit':code,'start_ns':start,'end_ns':time.time_ns(),'inputs_before':{str(p):h for p,h in PINS.items()},'inputs_after':{str(p):sha(p) for p in PINS},'wrapper_sha256_before':wrapper_before,'wrapper_sha256_after':sha(__file__),'stdout_sha256':sha(O/'stdout'),'stderr_sha256':sha(O/'stderr'),'child_result_sha256':sha(child/'result.json') if (child/'result.json').is_file() else None}
tmp=O/'terminal.tmp';tmp.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');os.replace(tmp,O/'terminal.json')
print(json.dumps({'exit':code,'inputs_stable':r['inputs_before']==r['inputs_after'],'wrapper_stable':r['wrapper_sha256_before']==r['wrapper_sha256_after'],'terminal_sha256':sha(O/'terminal.json')}))
if code or r['inputs_before']!=r['inputs_after'] or r['wrapper_sha256_before']!=r['wrapper_sha256_after']:raise SystemExit(1)
