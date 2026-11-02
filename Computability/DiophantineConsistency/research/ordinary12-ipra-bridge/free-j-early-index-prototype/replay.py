#!/usr/bin/env python3
"""Replay early free-J Pell index using fresh common-provider inputs."""
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('replay requires Python assertions enabled')
HERE=Path(__file__).resolve().parent; H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
INNER=HERE.parent/'free-j-pell-indices-prototype/replay.py'
SOURCES={'FreeJEarlyWindow':(HERE.parent/'free-j-early-window-prototype/FreeJEarlyWindow.lean','d94fc03938028ece937495de5b376bc13c71330b9502ddc235fb96fa4c4048bb',1,['FreeJFirstTransport','ArithmeticAdaptiveRankWindow2011']),
'FreeJEarlyIndex':(HERE/'FreeJEarlyIndex.lean','4f78abd78a895cc3d4e672e618d343b5e4c053a6489aba09bc5c9a20c7741adc',2,['FreeJPellIndices','FreeJEarlyWindow','ArithmeticAdaptiveEarlyIndex2011'])}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--receipt',type=Path,required=True);a=ap.parse_args();output=a.output.absolute()
 if output.exists() or output.is_symlink() or a.receipt.exists() or a.receipt.is_symlink():raise ValueError('refusing overwrite')
 for source,digest,_,_ in SOURCES.values():
  if H(source)!=digest:raise ValueError(('source drift',str(source)))
 inputs={str(x):H(x) for x in (INNER,Path(__file__))}|{str(x):H(x) for x,_,_,_ in SOURCES.values()}
 output.mkdir(parents=True);inner_out=output/'pell';inner_receipt=output/'pell-receipt.json'
 inner=subprocess.run([sys.executable,str(INNER),'--output',str(inner_out),'--receipt',str(inner_receipt)],text=True,capture_output=True)
 if inner.returncode:raise ValueError(('pell replay',inner.stdout,inner.stderr))
 prior=json.loads(inner_receipt.read_text())
 if prior['status']!='PASS_BOUNDED_FREEJ_PELL_INDICES':raise ValueError('invalid pell receipt')
 lib=inner_out/'rank/rank/rank/rank/freej/concrete/composed/base/lib';module=lib/'DiophantineConsistency';seed=inner_out/'FreeJPellIndices.olean';dst=module/'FreeJPellIndices.olean'
 if H(seed)!=prior['object_sha256'] or dst.exists() or dst.is_symlink():raise ValueError('invalid pell seed')
 shutil.copyfile(seed,dst);generated={'FreeJPellIndices':H(dst)};env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(n,None)
 env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);rows=[]
 for name,(source,digest,count,names) in SOURCES.items():
  root=output/name/'src';src=root/'DiophantineConsistency'/f'{name}.lean';src.parent.mkdir(parents=True);shutil.copyfile(source,src);obj=module/f'{name}.olean'
  if obj.exists() or obj.is_symlink():raise ValueError(('existing object',name))
  cmd=[str(LEAN),'-M8000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)];p=subprocess.run(cmd,env=env,text=True,capture_output=True);out=p.stdout+p.stderr
  if p.returncode or 'sorryAx' in out or 'warning:' in out or out.count('depends on axioms:')!=count:raise ValueError(('Lean failure',name,p.stdout,p.stderr))
  deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True);expect={str(PACKAGE/'Init.olean')}|{str(module/f'{x}.olean') for x in names}
  if deps.returncode or set(deps.stdout.splitlines())!=expect:raise ValueError(('deps',name,deps.stdout,deps.stderr))
  generated[name]=H(obj)
  for x,h in generated.items():
   if H(module/f'{x}.olean')!=h:raise ValueError(('generated drift',x))
  rows.append({'module':name,'lean_exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'command':cmd,'object_sha256':H(obj),'source_sha256':H(src),'deps_exit_code':deps.returncode,'deps_stdout':deps.stdout})
 if H(seed)!=prior['object_sha256'] or {x:H(x) for x in inputs}!=inputs:raise ValueError('input drift')
 base=prior['inner_receipt']['inner_receipt']['inner_receipt']['inner_receipt']
 for path,meta in base['seed_links'].items():
  q=Path(path);target=Path(meta['source'])
  if not q.is_symlink() or q.resolve()!=target or H(target)!=meta['sha256']:raise ValueError(('seed drift',path))
 for path in base['absent_parent_paths']:
  q=Path(path)
  if q.exists() or q.is_symlink():raise ValueError(('companion appeared',path))
 for path,digest in base['pinned_inputs'].items():
  if H(path)!=digest:raise ValueError(('parent pin drift',path))
 result={'status':'PASS_BOUNDED_FREEJ_EARLY_INDEX','inner_exit_code':inner.returncode,'inner_stdout':inner.stdout,'inner_receipt_sha256':H(inner_receipt),'inner_receipt':prior,'generated_objects':generated,'modules':rows,'inputs_sha256':inputs,'scope':'Single-author historical model early first-index residue and lower bound, with explicit mask assumptions; no index comparison, final rank, fixed-port interpretation, checker calibration or iPRA proof.'}
 with a.receipt.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_BOUNDED_FREEJ_EARLY_INDEX',H(a.receipt))
if __name__=='__main__':main()
