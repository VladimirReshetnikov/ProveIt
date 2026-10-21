#!/usr/bin/env python3
"""Eight reviewed Source149 leaves; no manifest wrapper or ancestor replay."""
from pathlib import Path
import argparse,subprocess,shutil,hashlib,json,os,time,sys

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
 packet=args.packet.resolve();out=args.output.resolve();out.mkdir(exist_ok=False)
 copy=out/'copy';shutil.copytree(packet,copy)
 logs=out/'logs';logs.mkdir();result=out/'results';result.mkdir()
 jobs=[
 ('logic-shared',['theory/check_classical_compact.py','theory/dominated_rho8_full_certificate.json']),
 ('logic-independent',['audits/audit_classical_independent.py','theory/dominated_rho8_full_certificate.json']),
 ('source-build',['source/build_dominated_source.py','source/baseline_sites219.json',str(result/'source'),'--common','--equivalent','source/sites218.json']),
 ('source-independent',['audits/verify_source_schedule.py','source/baseline_sites219.json','source/sites218.json','--common']),
 ('table-reconstruction',['binary/code/rebuild_table.py','binary/machine/k219.baseline.native.tm','binary/machine/transition_recipe.json',str(result/'rebuilt.native.tm')]),
 ('compact-bijection',['audits/audit_compact.py','binary/machine/k218.native.tm','binary/machine/k218.compact.tm','binary/machine/transition_recipe.json']),
 ('blank-independent',['audits/audit_blank_independent.py','binary/machine/k218.native.tm','binary/provenance/unfolded221.reference.tm']),
 ('startup-and-universal-runtime',['binary/code/validate_native.py','binary/machine/k218.native.tm','binary/machine/sites218.json',str(result/'runtime')]),
 ]
 inputs=set()
 for _,argv in jobs:
  for x in argv:
   if (copy/x).is_file():inputs.add(x)
 inputs.update(['binary/code/runtime/symbolic_runtime.py','binary/code/runtime/independent_runtime.py','binary/code/inputs/legacy_mapping.json'])
 before={p:sha(copy/p)for p in sorted(inputs)}
 record=dict(status='RUNNING',runner_source=dict(path=str(Path(__file__).resolve()),sha256=sha(Path(__file__))),original_packet=str(packet),disposable_copy=str(copy),input_pins_before=before,jobs=[],scope='Selected finite forward proof/source/table/startup checks and one complete arbitrary-natural runtime derivation. No manifest validation, proof search, ancestors or proof-assistant execution.')
 target=out/'actual.json';target.write_text(json.dumps(record,indent=2)+'\n')
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONOPTIMIZE='',B245_OUTPUT=str(result/'unused-runtime-default'))
 for name,argv in jobs:
  cmd=[sys.executable,'-B',*argv];limit=240 if name=='startup-and-universal-runtime'else 45
  started=time.monotonic();timed_out=False
  with (logs/(name+'.stdout')).open('wb')as stdout,(logs/(name+'.stderr')).open('wb')as stderr:
   try:p=subprocess.run(cmd,cwd=copy,env=env,stdout=stdout,stderr=stderr,timeout=limit);rc=p.returncode
   except subprocess.TimeoutExpired:timed_out=True;rc=None
  item=dict(name=name,argv=cmd,cwd=str(copy),timeout_seconds=limit,seconds=time.monotonic()-started,returncode=rc,timed_out=timed_out,stdout=str(logs/(name+'.stdout')),stderr=str(logs/(name+'.stderr')))
  item['stdout_sha256']=sha(Path(item['stdout']));item['stderr_sha256']=sha(Path(item['stderr']))
  record['jobs'].append(item);target.write_text(json.dumps(record,indent=2)+'\n')
  print(json.dumps(item),flush=True)
  if rc!=0 or timed_out:break
 record['input_pins_after']={p:sha(copy/p)for p in sorted(inputs)}
 record['inputs_unchanged']=record['input_pins_before']==record['input_pins_after']
 record['status']='SELECTED_LEAVES_EXITED_ZERO'if len(record['jobs'])==len(jobs)and all(x['returncode']==0 and not x['timed_out']for x in record['jobs'])and record['inputs_unchanged']else'SELECTED_LEAF_FAILURE'
 target.write_text(json.dumps(record,indent=2)+'\n')
 print(record['status'],flush=True)
 return 0 if record['status']=='SELECTED_LEAVES_EXITED_ZERO'else 1
if __name__=='__main__':raise SystemExit(main())
