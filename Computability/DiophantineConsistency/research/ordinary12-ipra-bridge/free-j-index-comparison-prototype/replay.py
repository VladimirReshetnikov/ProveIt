#!/usr/bin/env python3
"""Replay free-J Pell-index comparison over one fresh historical provider."""
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('replay requires Python assertions enabled')
HERE=Path(__file__).resolve().parent;H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
INNER=HERE.parent/'free-j-early-index-prototype/replay.py';SOURCE=HERE/'FreeJIndexComparison.lean';SOURCE_SHA='2b00bc90f94de730da50d856a5af7052918081992988464dc4d30a664d8683e4'
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--receipt',type=Path,required=True);a=ap.parse_args();output=a.output.absolute()
 if output.exists() or output.is_symlink() or a.receipt.exists() or a.receipt.is_symlink():raise ValueError('refusing overwrite')
 if H(SOURCE)!=SOURCE_SHA:raise ValueError('source drift')
 inputs={str(x):H(x) for x in (INNER,SOURCE,Path(__file__))};output.mkdir(parents=True);inner_out=output/'early';inner_receipt=output/'early-receipt.json'
 inner=subprocess.run([sys.executable,str(INNER),'--output',str(inner_out),'--receipt',str(inner_receipt)],text=True,capture_output=True)
 if inner.returncode:raise ValueError(('early replay',inner.stdout,inner.stderr))
 prior=json.loads(inner_receipt.read_text())
 if prior['status']!='PASS_BOUNDED_FREEJ_EARLY_INDEX':raise ValueError('invalid early receipt')
 lib=inner_out/'pell/rank/rank/rank/rank/freej/concrete/composed/base/lib';module=lib/'DiophantineConsistency'
 for n,d in prior['generated_objects'].items():
  if H(module/f'{n}.olean')!=d:raise ValueError(('generated input drift',n))
 root=output/'src';src=root/'DiophantineConsistency/FreeJIndexComparison.lean';src.parent.mkdir(parents=True);shutil.copyfile(SOURCE,src);obj=output/'FreeJIndexComparison.olean'
 env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(n,None)
 env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);cmd=[str(LEAN),'-M8000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)];p=subprocess.run(cmd,env=env,text=True,capture_output=True);out=p.stdout+p.stderr
 if p.returncode or 'sorryAx' in out or 'warning:' in out or out.count('depends on axioms:')!=2:raise ValueError(('Lean failure',p.stdout,p.stderr))
 deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True);expect={str(PACKAGE/'Init.olean'),str(module/'FreeJEarlyIndex.olean'),str(module/'ArithmeticAdaptiveIndexComparison2011.olean')}
 if deps.returncode or set(deps.stdout.splitlines())!=expect:raise ValueError(('deps',deps.stdout,deps.stderr))
 for n,d in prior['generated_objects'].items():
  if H(module/f'{n}.olean')!=d:raise ValueError(('generated input drift',n))
 if {x:H(x) for x in inputs}!=inputs:raise ValueError('input drift')
 base=prior['inner_receipt']['inner_receipt']['inner_receipt']['inner_receipt']['inner_receipt']
 for path,meta in base['seed_links'].items():
  q=Path(path);target=Path(meta['source'])
  if not q.is_symlink() or q.resolve()!=target or H(target)!=meta['sha256']:raise ValueError(('seed drift',path))
 for path in base['absent_parent_paths']:
  q=Path(path)
  if q.exists() or q.is_symlink():raise ValueError(('companion appeared',path))
 for path,digest in base['pinned_inputs'].items():
  if H(path)!=digest:raise ValueError(('parent pin drift',path))
 result={'status':'PASS_BOUNDED_FREEJ_INDEX_COMPARISON','inner_exit_code':inner.returncode,'inner_stdout':inner.stdout,'inner_receipt_sha256':H(inner_receipt),'inner_receipt':prior,'lean_exit_code':p.returncode,'lean_stdout':p.stdout,'lean_stderr':p.stderr,'lean_command':cmd,'object_sha256':H(obj),'deps_exit_code':deps.returncode,'deps_stdout':deps.stdout,'inputs_sha256':inputs,'scope':'Single-author model comparison of free-J Pell indices with explicit mask bounds. No final index equality, actual port interpretation, checker calibration, full pair replay or iPRA proof.'}
 with a.receipt.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_BOUNDED_FREEJ_INDEX_COMPARISON',H(a.receipt))
if __name__=='__main__':main()
