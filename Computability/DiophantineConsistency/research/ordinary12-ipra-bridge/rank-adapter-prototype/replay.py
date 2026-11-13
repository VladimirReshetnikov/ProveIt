#!/usr/bin/env python3
"""Historical guarded replay of conditional compact44 cancellation adapter."""
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
if not __debug__: raise RuntimeError('replay requires Python assertions enabled')
HERE=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
PARENT=Path('/tmp/ipra-aq29-fresh-project-pair'); SNAPSHOT=Path('/tmp/ipra-aq29-fresh-source-closure-v2')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'); LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SOURCE=HERE/'Ordinary12RankAdapter.lean'; INNER=HERE.parent/'free-j-prototype/replay.py'
PIN={SOURCE:'0db8060c5c0a130a66944775f21c1cc7ff324c5737afc712e47c0af50df20ea5',PARENT/'pair-state.json':'04832cc18c11ad9da49d2cfc0c865baed07a18ace44d1de9d8319b150890e7dd',SNAPSHOT/'manifest.json':'63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
def verify():
 for p,digest in PIN.items():
  if H(p)!=digest:raise ValueError(('pin drift',str(p)))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--receipt',type=Path,required=True);a=ap.parse_args();verify()
 output=a.output.absolute()
 if output.exists() or output.is_symlink() or a.receipt.exists() or a.receipt.is_symlink():raise ValueError('refusing overwrite')
 for p in (PARENT,SNAPSHOT,PACKAGE,HERE):
  if output.resolve().is_relative_to(p.resolve()) or p.resolve().is_relative_to(output.resolve()):raise ValueError('protected output overlap')
 scriptpins={str(p):H(p) for p in (INNER,Path(__file__))}
 pair=json.loads((PARENT/'pair-state.json').read_text());author=next(x for x in pair['runs'] if x['label']=='author');state_path=PARENT/'author/state.json';state_hash=H(state_path)
 if pair['status']!='MATCHED_PASS' or author['exit']!=0 or state_hash!=author['builder_state_sha256']:raise ValueError('invalid parent')
 state=json.loads(state_path.read_text()); manifest=json.loads((SNAPSHOT/'manifest.json').read_text()); seen=set();todo=['DiophantineConsistency.ArithmeticAdaptiveFactorThree2011','DiophantineConsistency.ArithmeticAdaptiveMersenne2011']
 while todo:
  name=todo.pop()
  if name in seen or name not in manifest['sources']:continue
  seen.add(name);entry=manifest['sources'][name]
  if H(SNAPSHOT/entry['snapshot_path'])!=entry['sha256']:raise ValueError(('source drift',name))
  todo.extend(entry['imports'])
 if len(seen)!=62:raise ValueError(('unexpected historical source closure',len(seen)))
 output.mkdir(parents=True);inner_out=output/'freej';inner_receipt=output/'freej-receipt.json'
 inner=subprocess.run([sys.executable,str(INNER),'--output',str(inner_out),'--receipt',str(inner_receipt)],text=True,capture_output=True)
 if inner.returncode:raise ValueError(('free J replay',inner.stdout,inner.stderr))
 prior=json.loads(inner_receipt.read_text())
 if prior['status']!='PASS_BOUNDED_FREE_J_95_FACTOR_SPLIT':raise ValueError('invalid free J receipt')
 lib=inner_out/'concrete/composed/base/lib';parent_lib=PARENT/'author/lib';present={};absent=[]
 for name in sorted(seen):
  for path,meta in state['outputs'][name].items():
   src=Path(path)
   if not src.is_relative_to(parent_lib):raise ValueError('parent path escape')
   dst=lib/src.relative_to(parent_lib)
   if meta is None:
    if src.exists() or src.is_symlink() or dst.exists() or dst.is_symlink():raise ValueError(('unexpected companion',path))
    absent.append(path)
   else:
    if src.is_symlink() or not src.is_file() or str(src.resolve())!=meta['realpath'] or H(src)!=meta['sha256']:raise ValueError(('object drift',path))
    dst.parent.mkdir(parents=True,exist_ok=True)
    if dst.is_symlink():
     if dst.resolve()!=src:raise ValueError(('different inherited object',str(dst)))
    elif dst.exists():raise ValueError(('unexpected local object',str(dst)))
    else:dst.symlink_to(src)
    present[str(dst)]={'source':str(src),'sha256':meta['sha256']}
 root=output/'src';src=root/'DiophantineConsistency/Ordinary12RankAdapter.lean';src.parent.mkdir(parents=True);shutil.copyfile(SOURCE,src);obj=output/'Ordinary12RankAdapter.olean'
 env=os.environ.copy()
 for n in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(n,None)
 env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
 cmd=[str(LEAN),'-M8000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)];proc=subprocess.run(cmd,env=env,text=True,capture_output=True);out=proc.stdout+proc.stderr
 if proc.returncode or 'sorryAx' in out or 'warning:' in out or out.count('depends on axioms:')!=2:raise ValueError(('Lean failed',proc.stdout,proc.stderr))
 deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True)
 expect={str(PACKAGE/'Init.olean')}|{str(lib/'DiophantineConsistency'/f'{x}.olean') for x in ('Ordinary12FreeJ','ArithmeticAdaptiveFactorThree2011','ArithmeticAdaptiveMersenne2011')}
 if deps.returncode or set(deps.stdout.splitlines())!=expect:raise ValueError(('deps',deps.stdout,deps.stderr))
 verify()
 if H(state_path)!=state_hash or {p:H(p) for p in scriptpins}!=scriptpins:raise ValueError('input drift')
 for name in seen:
  e=manifest['sources'][name]
  if H(SNAPSHOT/e['snapshot_path'])!=e['sha256']:raise ValueError(('source drift',name))
 for path,meta in present.items():
  p=Path(path);source=Path(meta['source'])
  if not p.is_symlink() or p.resolve()!=source or H(source)!=meta['sha256']:raise ValueError(('seed drift',path))
 for path in absent:
  p=Path(path)
  if p.exists() or p.is_symlink():raise ValueError(('companion appeared',path))
 result={'status':'PASS_BOUNDED_CONDITIONAL_FREEJ_RANK_ADAPTER','source_closure':sorted(seen),'seed_links':present,'absent_parent_paths':absent,'parent_state_sha256':state_hash,'pinned_inputs':{str(p):d for p,d in PIN.items()},'script_hashes':scriptpins,'freej_replay_exit_code':inner.returncode,'freej_replay_stdout':inner.stdout,'freej_receipt_sha256':H(inner_receipt),'freej_receipt':prior,'lean_exit_code':proc.returncode,'lean_stdout':proc.stdout,'lean_stderr':proc.stderr,'lean_command':cmd,'object_sha256':H(obj),'deps_exit_code':deps.returncode,'deps_stdout':deps.stdout,'scope':'Single-author historical model theorem only. Assumes separate carrier divisibility hypotheses and the exact Mersenne exponent equality; no graph-to-carrier bindings, rank derivation, checker calibration, paired full replay or iPRA proof.'}
 with a.receipt.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_BOUNDED_CONDITIONAL_FREEJ_RANK_ADAPTER',H(a.receipt))
if __name__=='__main__':main()
