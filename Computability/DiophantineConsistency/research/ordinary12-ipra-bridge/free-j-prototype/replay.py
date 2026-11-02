#!/usr/bin/env python3
"""Replay the 95-row free-J factor split on a fresh historical overlay."""
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
if not __debug__: raise RuntimeError('replay requires Python assertions enabled')
HERE=Path(__file__).resolve().parent
H=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SOURCE=HERE/'Ordinary12FreeJ.lean'
SOURCE_SHA='542bb6913f5b7e6d1ef3cd9e430fcbee20ee727966d3bfc9f2b6d71c566ef96a'
def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--output',type=Path,required=True); ap.add_argument('--receipt',type=Path,required=True); a=ap.parse_args()
 output=a.output.absolute()
 if output.exists() or output.is_symlink() or a.receipt.exists() or a.receipt.is_symlink(): raise ValueError('refusing overwrite')
 if H(SOURCE)!=SOURCE_SHA: raise ValueError('source drift')
 inner_script=HERE.parent/'concrete-split-prototype/replay.py'; check_script=HERE/'check_graph.py'
 inputs={str(p):H(p) for p in (SOURCE,inner_script,check_script,Path(__file__))}
 check=subprocess.run([sys.executable,str(check_script)],capture_output=True,text=True)
 if check.returncode: raise ValueError(('graph check',check.stdout,check.stderr))
 output.mkdir(parents=True); inner_out=output/'concrete'; inner_receipt=output/'concrete-receipt.json'
 inner=subprocess.run([sys.executable,str(inner_script),'--output',str(inner_out),'--receipt',str(inner_receipt)],capture_output=True,text=True)
 if inner.returncode: raise ValueError(('concrete replay',inner.stdout,inner.stderr))
 prior=json.loads(inner_receipt.read_text())
 if prior['status']!='PASS_BOUNDED_ORDINARY12_CONCRETE_SPLIT': raise ValueError('invalid concrete receipt')
 lib=inner_out/'composed/base/lib'; module=lib/'DiophantineConsistency'; root=output/'src'; src=root/'DiophantineConsistency/Ordinary12FreeJ.lean'; src.parent.mkdir(parents=True); shutil.copyfile(SOURCE,src)
 obj=module/'Ordinary12FreeJ.olean'
 if obj.exists() or obj.is_symlink(): raise ValueError('existing object')
 env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'): env.pop(n,None)
 env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
 cmd=[str(LEAN),'-M8000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
 p=subprocess.run(cmd,env=env,capture_output=True,text=True); alltext=p.stdout+p.stderr
 if p.returncode or 'sorryAx' in alltext or 'warning:' in alltext or alltext.count('depends on axioms:')!=7: raise ValueError(('Lean failure',p.stdout,p.stderr))
 deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,capture_output=True,text=True)
 expect={str(PACKAGE/'Init.olean'),str(module/'Ordinary12Patterns.olean'),str(module/'Ordinary12FactorSplit.olean')}
 if deps.returncode or set(deps.stdout.splitlines())!=expect: raise ValueError(('deps',deps.stdout,deps.stderr))
 for name,digest in prior['generated_objects'].items():
  if H(module/f'{name}.olean')!=digest: raise ValueError(('generated object drift',name))
 base=prior['composed_receipt']['base_receipt']
 for link,meta in base['seed_links'].items():
  q=Path(link); target=Path(meta['source'])
  if not q.is_symlink() or q.resolve()!=target or H(target)!=meta['sha256']: raise ValueError(('seed drift',link))
 for name in base['absent_parent_paths']:
  q=Path(name)
  if q.exists() or q.is_symlink(): raise ValueError(('companion appeared',name))
 if {x:H(x) for x in inputs}!=inputs: raise ValueError('source drift')
 result={'status':'PASS_BOUNDED_FREE_J_95_FACTOR_SPLIT','graph_check_exit_code':check.returncode,'graph_check_stdout':check.stdout,'inner_exit_code':inner.returncode,'inner_stdout':inner.stdout,'inner_receipt_sha256':H(inner_receipt),'inner_receipt':prior,'lean_exit_code':p.returncode,'lean_stdout':p.stdout,'lean_stderr':p.stderr,'lean_command':cmd,'object_sha256':H(obj),'deps_exit_code':deps.returncode,'deps_stdout':deps.stdout,'inputs_sha256':inputs,'scope':'Historical single-author model result for arbitrary integer ports and free J; no compact44 checker calibration, rank/congruence recovery, matched project replay or iPRA derivation.'}
 with a.receipt.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_BOUNDED_FREE_J_95_FACTOR_SPLIT',H(a.receipt))
if __name__=='__main__':main()
