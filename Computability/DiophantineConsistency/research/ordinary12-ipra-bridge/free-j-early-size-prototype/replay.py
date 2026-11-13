#!/usr/bin/env python3
"""Replay the free-J early-size corollary over the historical provider."""
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('replay requires Python assertions enabled')
HERE=Path(__file__).resolve().parent;H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
INNER=HERE.parent/'free-j-index-comparison-prototype/replay.py';SOURCE=HERE/'FreeJEarlySize.lean';SOURCE_SHA='0e670e6d0cd8431893b5ccf3267d9857eb8d7301af0acb49acb04433e07c44fb'
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--receipt',type=Path,required=True);a=ap.parse_args();output=a.output.absolute()
 if output.exists() or output.is_symlink() or a.receipt.exists() or a.receipt.is_symlink():raise ValueError('refusing overwrite')
 if H(SOURCE)!=SOURCE_SHA:raise ValueError('source drift')
 inputs={str(x):H(x) for x in (INNER,SOURCE,Path(__file__))};output.mkdir(parents=True);inner_out=output/'comparison';inner_receipt=output/'comparison-receipt.json'
 inner=subprocess.run([sys.executable,str(INNER),'--output',str(inner_out),'--receipt',str(inner_receipt)],text=True,capture_output=True)
 if inner.returncode:raise ValueError(('comparison replay',inner.stdout,inner.stderr))
 prior=json.loads(inner_receipt.read_text())
 if prior['status']!='PASS_BOUNDED_FREEJ_INDEX_COMPARISON':raise ValueError('invalid comparison receipt')
 lib=inner_out/'early/pell/rank/rank/rank/rank/freej/concrete/composed/base/lib';module=lib/'DiophantineConsistency';seed=inner_out/'FreeJIndexComparison.olean';dst=module/'FreeJIndexComparison.olean'
 if H(seed)!=prior['object_sha256'] or dst.exists() or dst.is_symlink():raise ValueError('invalid comparison seed')
 shutil.copyfile(seed,dst)
 root=output/'src';src=root/'DiophantineConsistency/FreeJEarlySize.lean';src.parent.mkdir(parents=True);shutil.copyfile(SOURCE,src);obj=output/'FreeJEarlySize.olean'
 env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(n,None)
 env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);cmd=[str(LEAN),'-M8000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)];p=subprocess.run(cmd,env=env,text=True,capture_output=True);out=p.stdout+p.stderr
 if p.returncode or 'sorryAx' in out or 'warning:' in out or out.count('depends on axioms:')!=1:raise ValueError(('Lean failure',p.stdout,p.stderr))
 deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True);expect={str(PACKAGE/'Init.olean'),str(dst),str(module/'ArithmeticPellResidueAux.olean')}
 if deps.returncode or set(deps.stdout.splitlines())!=expect:raise ValueError(('deps',deps.stdout,deps.stderr))
 if H(seed)!=prior['object_sha256'] or H(dst)!=prior['object_sha256'] or {x:H(x) for x in inputs}!=inputs:raise ValueError('input drift')
 base=prior
 while 'seed_links' not in base:
  if 'inner_receipt' not in base:raise ValueError('missing historical seed guard')
  base=base['inner_receipt']
 for path,meta in base['seed_links'].items():
  q=Path(path);target=Path(meta['source'])
  if not q.is_symlink() or q.resolve()!=target or H(target)!=meta['sha256']:raise ValueError(('seed drift',path))
 for path in base['absent_parent_paths']:
  q=Path(path)
  if q.exists() or q.is_symlink():raise ValueError(('companion appeared',path))
 for path,digest in base['pinned_inputs'].items():
  if H(path)!=digest:raise ValueError(('parent pin drift',path))
 result={'status':'PASS_BOUNDED_FREEJ_EARLY_SIZE','inner_exit_code':inner.returncode,'inner_stdout':inner.stdout,'inner_receipt_sha256':H(inner_receipt),'inner_receipt':prior,'comparison_seed_sha256':H(dst),'lean_exit_code':p.returncode,'lean_stdout':p.stdout,'lean_stderr':p.stderr,'lean_command':cmd,'object_sha256':H(obj),'deps_exit_code':deps.returncode,'deps_stdout':deps.stdout,'inputs_sha256':inputs,'scope':'Single-author historical model early-size result, with explicit mask bounds. No ordinary strong norm, fixed-port interpretation, checker calibration, full pair replay or iPRA proof.'}
 with a.receipt.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_BOUNDED_FREEJ_EARLY_SIZE',H(a.receipt))
if __name__=='__main__':main()
