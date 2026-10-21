#!/usr/bin/env python3
"""Regression/negative controls in disposable copies, not a kernel check."""
from validation_guard import ensure_safe_runtime, SOURCE_SHA256
ensure_safe_runtime()
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile
HERE=Path(__file__).resolve().parent
SCRIPTS=['prototype.py','compare_flat_cfg.py','analyze_cfg_rewrites.py']
HELPERS=SCRIPTS+['validation_guard.py']
normal_env=dict(os.environ);normal_env.pop('PYTHONOPTIMIZE',None)

def run(args,cwd,env=normal_env):
 r=subprocess.run([sys.executable]+args,cwd=cwd,env=env,text=True,capture_output=True,timeout=60)
 return {'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr}

def demand(condition,message):
 if not condition:raise RuntimeError(message)

def main():
 formal_before={p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in HERE.glob('*.v')}
 receipts=[]
 with tempfile.TemporaryDirectory(prefix='rocq-checker-hardening-')as td:
  tmp=Path(td);src=tmp/'snapshot/rocq/rocq-extension/coq/215';src.mkdir(parents=True)
  for name in HELPERS:shutil.copyfile(HERE/name,tmp/name)
  originals={name:(HERE/'snapshot/rocq/rocq-extension/coq/215'/name).read_bytes()for name in SOURCE_SHA256}
  for name,data in originals.items():(src/name).write_bytes(data)
  for script in SCRIPTS:
   r=run([script],tmp);demand(r['exit_code']==0,'Ordinary isolated run failed: '+script)
   receipts.append({'test':'ordinary_pinned_run','script':script,'passed':True,'exit_code':0})
   for flag in ['-O','-OO']:
    r=run([flag,script],tmp);demand(r['exit_code']!=0 and 'UNSAFE_PYTHON_OPTIMIZATION' in r['stderr'],'Optimization accepted: '+script+flag)
    receipts.append({'test':'optimization_rejection','script':script,'flag':flag,'passed':True,**r})
   for value in ['0','1','2']:
    r=run([script],tmp,dict(normal_env,PYTHONOPTIMIZE=value));demand(r['exit_code']!=0 and 'UNSAFE_PYTHON_OPTIMIZATION' in r['stderr'],'Environment accepted: '+script+value)
    receipts.append({'test':'environment_rejection','script':script,'PYTHONOPTIMIZE':value,'passed':True,**r})
  r=run(['-O','-c','import prototype'],tmp);demand(r['exit_code']!=0 and 'UNSAFE_PYTHON_OPTIMIZATION' in r['stderr'],'Optimized helper import accepted')
  receipts.append({'test':'optimized_helper_import_rejection','passed':True,**r})
  mutations=[('Cert215Offsets.v',b'0%Z',b'1%Z','same_shape_offset'),
             ('Prog215.v',b'(CD 8, CB 1)',b'(CD 7, CB 1)','same_shape_test_register'),
             ('DagPerm.v',b'188 => (EInc 6, EInc 7)',b'188 => (EInc 5, EInc 7)','same_shape_increment_register'),
             ('Cert215Offsets.v',b'false',b'FALSE_NOT_A_COQ_BOOL','malformed_boolean_token')]
  for name,old,new,label in mutations:
   demand(old in originals[name],'Mutation target absent')
   altered=originals[name].replace(old,new,1);(src/name).write_bytes(altered)
   for script in SCRIPTS:
    r=run([script],tmp);demand(r['exit_code']!=0 and 'SOURCE_SHA256_MISMATCH' in r['stderr'],'Changed source accepted: '+script+label)
    receipts.append({'test':'source_hash_rejection','script':script,'source':name,'mutation':label,'mutated_sha256':hashlib.sha256(altered).hexdigest(),'passed':True,**r})
   (src/name).write_bytes(originals[name])
  r=run(['-c',"import prototype; prototype.paths('true;FALSE_NOT_A_COQ_BOOL')"],tmp)
  demand(r['exit_code']!=0 and 'INVALID_BOOLEAN_TOKEN' in r['stderr'],'Direct Boolean parser accepted malformed token')
  receipts.append({'test':'strict_boolean_parser_rejection','passed':True,**r})
 for script in SCRIPTS:
  r=run([script],HERE);demand(r['exit_code']==0,'Ordinary final run failed: '+script)
  (HERE/(script[:-3]+'_hardened_validation.log')).write_text(r['stdout']+r['stderr'])
  receipts.append({'test':'ordinary_final_run','script':script,'passed':True,'exit_code':0})
 formal_after={p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in HERE.glob('*.v')}
 demand(formal_before==formal_after,'Formal source bytes changed')
 result={'status':'PASS_FAIL_CLOSED_REPRODUCIBILITY_CONTROLS_NOT_KERNEL_CHECK',
  'scope':'Rocq-owned Python checkers only; no formal .v semantic changes or kernel execution.',
  'source_pins':SOURCE_SHA256,'all_tests_passed':True,'test_count':len(receipts),
  'formal_v_files_unchanged':formal_before==formal_after,'formal_v_sha256':formal_after,
  'tests':receipts}
 (HERE/'hardening_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items()if k!='tests'},indent=2))
if __name__=='__main__':main()
