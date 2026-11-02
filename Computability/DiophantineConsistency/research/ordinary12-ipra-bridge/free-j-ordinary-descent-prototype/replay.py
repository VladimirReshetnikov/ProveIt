#!/usr/bin/env python3
"""Replay the free-J ordinary residual and cleared identities over the historical rank overlay."""
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('replay requires Python assertions enabled')
HERE=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SOURCE=HERE/'FreeJNormZero.lean';INNER=HERE.parent/'rank-adapter-prototype/replay.py'
SOURCE_SHA='995b432150625401e8ccb860e0b7013ee4352461b6698dce8bd7d5388ea2c399'
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--receipt',type=Path,required=True);a=ap.parse_args();output=a.output.absolute()
 if output.exists() or output.is_symlink() or a.receipt.exists() or a.receipt.is_symlink():raise ValueError('refusing overwrite')
 if H(SOURCE)!=SOURCE_SHA:raise ValueError('source drift')
 inputs={str(x):H(x) for x in (SOURCE,INNER,Path(__file__))}
 output.mkdir(parents=True);inner_out=output/'rank';inner_receipt=output/'rank-receipt.json'
 inner=subprocess.run([sys.executable,str(INNER),'--output',str(inner_out),'--receipt',str(inner_receipt)],text=True,capture_output=True)
 if inner.returncode:raise ValueError(('rank replay failed',inner.stdout,inner.stderr))
 prior=json.loads(inner_receipt.read_text())
 if prior['status']!='PASS_BOUNDED_CONDITIONAL_FREEJ_RANK_ADAPTER':raise ValueError('invalid rank receipt')
 lib=inner_out/'freej/concrete/composed/base/lib';module=lib/'DiophantineConsistency';seed=inner_out/'Ordinary12RankAdapter.olean';dst=module/'Ordinary12RankAdapter.olean'
 if H(seed)!=prior['object_sha256'] or dst.exists() or dst.is_symlink():raise ValueError('invalid rank seed')
 shutil.copyfile(seed,dst)
 if H(dst)!=prior['object_sha256']:raise ValueError('seed copy drift')
 root=output/'src';src=root/'DiophantineConsistency/FreeJNormZero.lean';src.parent.mkdir(parents=True);shutil.copyfile(SOURCE,src);obj=output/'FreeJNormZero.olean'
 env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(n,None)
 env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
 cmd=[str(LEAN),'-M8000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)];p=subprocess.run(cmd,env=env,text=True,capture_output=True);out=p.stdout+p.stderr
 if p.returncode or 'sorryAx' in out or 'warning:' in out or out.count('depends on axioms:')!=5:raise ValueError(('Lean failure',p.stdout,p.stderr))
 deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True)
 expect={str(PACKAGE/'Init.olean'),str(module/'Ordinary12FreeJ.olean')}
 if deps.returncode or set(deps.stdout.splitlines())!=expect:raise ValueError(('deps',deps.stdout,deps.stderr))
 if H(seed)!=prior['object_sha256'] or H(dst)!=prior['object_sha256'] or {x:H(x) for x in inputs}!=inputs:raise ValueError('input drift')
 for path,meta in prior['seed_links'].items():
  q=Path(path);target=Path(meta['source'])
  if not q.is_symlink() or q.resolve()!=target or H(target)!=meta['sha256']:raise ValueError(('seed drift',path))
 for path in prior['absent_parent_paths']:
  q=Path(path)
  if q.exists() or q.is_symlink():raise ValueError(('companion appeared',path))
 for path,digest in prior['pinned_inputs'].items():
  if H(path)!=digest:raise ValueError(('parent pin drift',path))
 result={'status':'PASS_BOUNDED_FREEJ_ORDINARY_IDENTITIES','inner_exit_code':inner.returncode,'inner_stdout':inner.stdout,'inner_receipt_sha256':H(inner_receipt),'inner_receipt':prior,'rank_seed_sha256':H(dst),'lean_exit_code':p.returncode,'lean_stdout':p.stdout,'lean_stderr':p.stderr,'lean_command':cmd,'object_sha256':H(obj),'deps_exit_code':deps.returncode,'deps_stdout':deps.stdout,'inputs_sha256':inputs,'scope':'Single-author model residual zero and natural-parameter cleared signed-pair identity, plus universal ring identities. No signed graph-parameter substitution, denominator integrality, strong norm, checker calibration or iPRA proof.'}
 with a.receipt.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_BOUNDED_FREEJ_ORDINARY_IDENTITIES',H(a.receipt))
if __name__=='__main__':main()
