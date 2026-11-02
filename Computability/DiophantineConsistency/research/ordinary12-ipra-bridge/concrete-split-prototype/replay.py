#!/usr/bin/env python3
"""Replay the literal-to-concrete-unit split over a fresh historical overlay."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
if not __debug__:
    raise RuntimeError('replay guards require Python assertions enabled')
HERE=Path(__file__).resolve().parent
H=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SOURCES={
 'Ordinary12Literal':(HERE.parent/'literal-prototype/Ordinary12Literal.lean','23a22eebc33d262e1b4c134c6072e808c002aac31a627def951bc753d3e96709'),
 'Ordinary12Patterns':(HERE/'Ordinary12Patterns.lean','5b37fb90f66d1ac0775018ddc7b05c26bf6c9bd4615ff794318613a97c31b25a'),
 'Ordinary12ConcreteSplit':(HERE/'Ordinary12ConcreteSplit.lean','5e512b0cd623d0875523b55b56301692891942a8ab66561262b0f94462627548')}

def main():
 parser=argparse.ArgumentParser(); parser.add_argument('--output',type=Path,required=True); parser.add_argument('--receipt',type=Path,required=True); a=parser.parse_args()
 output=a.output.absolute()
 if output.exists() or output.is_symlink() or a.receipt.exists() or a.receipt.is_symlink(): raise ValueError('refusing overwrite')
 for path,digest in SOURCES.values():
  if H(path)!=digest: raise ValueError(('source drift',str(path)))
 scripts=[HERE/'check_binding.py',HERE.parent/'literal-prototype/check_literal.py',HERE.parent/'model-prototype/replay_composed.py',Path(__file__)]
 inputs={str(p):H(p) for p in scripts}|{str(p):H(p) for p,_ in SOURCES.values()}
 check=subprocess.run([sys.executable,str(scripts[0])],capture_output=True,text=True)
 if check.returncode: raise ValueError(('binding check',check.stdout,check.stderr))
 output.mkdir(parents=True); base=output/'composed'; base_receipt=output/'composed-receipt.json'
 inner=subprocess.run([sys.executable,str(scripts[2]),'--output',str(base),'--receipt',str(base_receipt)],capture_output=True,text=True)
 if inner.returncode: raise ValueError(('composed replay',inner.stdout,inner.stderr))
 prior=json.loads(base_receipt.read_text())
 if prior['status']!='PASS_BOUNDED_COMPOSED_MODEL_SPLIT': raise ValueError('invalid composed receipt')
 lib=base/'base/lib'; module=lib/'DiophantineConsistency'; env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'): env.pop(n,None)
 env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
 generated=dict(prior['generated_objects']); rows=[]
 expected={'Ordinary12Literal':(['ArithmeticAdaptiveFactorMagnitude2011'],3), 'Ordinary12Patterns':(['ArithmeticAdaptiveFactorUnits2011'],3), 'Ordinary12ConcreteSplit':(['Ordinary12Literal','Ordinary12Patterns','Ordinary12FactorSplit'],4)}
 for name,(source,_) in SOURCES.items():
  root=output/name/'src'; src=root/'DiophantineConsistency'/f'{name}.lean'; src.parent.mkdir(parents=True); shutil.copyfile(source,src)
  obj=module/f'{name}.olean'
  if obj.exists() or obj.is_symlink(): raise ValueError(('existing output',name))
  cmd=[str(LEAN),'-M8000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
  proc=subprocess.run(cmd,env=env,capture_output=True,text=True); text=proc.stdout+proc.stderr
  names,reports=expected[name]
  if proc.returncode or 'sorryAx' in text or 'warning:' in text or text.count('depends on axioms:')!=reports: raise ValueError((name,proc.stdout,proc.stderr))
  dep=subprocess.run([str(LEAN),'--deps',str(src)],env=env,capture_output=True,text=True)
  expected_deps={str(PACKAGE/'Init.olean')}|{str(module/f'{n}.olean') for n in names}
  if dep.returncode or set(dep.stdout.splitlines())!=expected_deps: raise ValueError(('dependencies',name,dep.stdout,dep.stderr))
  generated[name]=H(obj)
  for n,digest in generated.items():
   if H(module/f'{n}.olean')!=digest: raise ValueError(('generated object drift',n))
  rows.append({'module':name,'exit_code':proc.returncode,'stdout':proc.stdout,'stderr':proc.stderr,'command':cmd,'source_sha256':H(src),'object_sha256':H(obj),'deps_exit_code':dep.returncode,'deps_stdout':dep.stdout})
 for link,meta in prior['base_receipt']['seed_links'].items():
  p=Path(link); target=Path(meta['source'])
  if not p.is_symlink() or p.resolve()!=target or H(target)!=meta['sha256']: raise ValueError(('seed drift',link))
 for name in prior['base_receipt']['absent_parent_paths']:
  p=Path(name)
  if p.exists() or p.is_symlink(): raise ValueError(('companion appeared',name))
 if {p:H(p) for p in inputs}!=inputs: raise ValueError('input drift')
 result={'status':'PASS_BOUNDED_ORDINARY12_CONCRETE_SPLIT','graph_check_exit_code':check.returncode,'graph_check_stdout':check.stdout,'composed_replay_exit_code':inner.returncode,'composed_replay_stdout':inner.stdout,'composed_receipt_sha256':H(base_receipt),'composed_receipt':prior,'generated_objects':generated,'modules':rows,'input_sha256':inputs,'scope':'Historical single-author model-level result for arbitrary integer ports. No compact44 checker calibration, rank recovery, paired project replay, dynamic dependency audit, or iPRA derivation.'}
 with a.receipt.open('x') as f: json.dump(result,f,indent=2,sort_keys=True); f.write('\n')
 print('PASS_BOUNDED_ORDINARY12_CONCRETE_SPLIT',H(a.receipt))
if __name__=='__main__': main()
