#!/usr/bin/env python3
"""Paired free-J main index uniqueness over the audited exact-index provider."""
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:
 raise RuntimeError('invoke with python3 -I -S, without optimization')
HERE=Path(__file__).resolve().parent;BASE=HERE.parent;ROOT=HERE.parents[2]
SOURCE=HERE/'FreeJMainIndexUnique.lean'; AUDIT=ROOT/'reviews/ordinary12-freej-exact-ordinary-independent-audit'
TABLE=BASE/'free-j-exact-ordinary-prototype'; PARENT=Path('/tmp/ipra-freej-exact-ordinary-pair-01')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'; LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'bb930c6646519e57eb0ecd0c30669096ec0d61155e89f847edfa33cf62de4cc0',
 AUDIT/'audit.py':'784b851906cb26c333731d840f5d49dad4364a447ee53bb201042ae490b2c644',
 AUDIT/'CHECK.json':'2e25209934dd515c324ccbb796647e43a698d128987b083c0686a977097dc86a',
 AUDIT/'terminal-observation.json':'a59d2119dae9f181c858371eb9e0ec150dd712f456f3287f270d98aa3e7fef7e',
 TABLE/'evidence/receipt.json':'fec23d0d6fdc8b66041bf67b41f10a80e8dc3b9d48bd0b7138cfb6bf19374c6c',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
EXPECTED="""'FreeJMainIndexUnique.graph_ordinate_index_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
"""
def verify():
 for p,h in PINS.items():
  if H(p)!=h:raise ValueError(('input drift',str(p)))
 obs=json.loads((AUDIT/'terminal-observation.json').read_text());audit=json.loads((AUDIT/'CHECK.json').read_text())
 if obs['audit_observed_exit_code'] or obs['receipt_sha256']!=PINS[AUDIT/'CHECK.json'] or audit['status']!='PASS_INDEPENDENT_FREEJ_EXACT_ORDINARY_AUDIT':raise ValueError('parent audit observation')
 cmd=[sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')];p=subprocess.run(cmd,capture_output=True,text=True,timeout=600)
 if p.returncode or p.stderr:raise ValueError(('parent audit rerun',p.returncode,p.stdout,p.stderr))
 if json.loads(p.stdout)!=audit:raise ValueError('parent audit output drift')
 return audit

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
 if out.parent.resolve()!=Path('/tmp').resolve() or not out.name.startswith('ipra-freej-main-index-unique-pair-') or os.path.lexists(out):raise ValueError('need fresh dedicated /tmp output')
 driver=H(__file__);before=verify();spec=importlib.util.spec_from_file_location('monitor',MONITOR);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
 out.mkdir();runs=[];parent=json.loads((TABLE/'evidence/receipt.json').read_text())
 for label in ('author','peer'):
  run=out/label;root=run/'src';root.mkdir(parents=True);src=root/'FreeJMainIndexUnique.lean';shutil.copyfile(SOURCE,src);lib=run/'lib';monitor.overlay(PARENT/label/'lib',lib)
  target=lib/'DiophantineConsistency/FreeJExactOrdinary.olean';seed=PARENT/label/'FreeJExactOrdinary.olean';pr=next(r for r in parent['runs'] if r['label']==label)
  if os.path.lexists(target) or H(seed)!=pr['object_sha256']:raise ValueError('parent object mismatch or collision')
  shutil.copyfile(seed,target);seedhash=H(target);env=os.environ.copy()
  for k in tuple(env):
   if k.startswith('PYTHON') or k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT','LEAN_SRC_PATH','LEAN_SYSROOT'):env.pop(k,None)
  env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120)
  expected={str(PACKAGE/'Init.olean'),str(target)}
  if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('deps',deps.returncode,deps.stdout,deps.stderr))
  obj=run/'FreeJMainIndexUnique.olean';log=run/'compiler.log';cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
  code,peak,reason=monitor.monitored(cmd,env,log);output=log.read_text()
  if code or reason or output!=EXPECTED or not obj.is_file() or H(src)!=PINS[SOURCE] or H(target)!=seedhash:raise ValueError(('compiler/result mismatch',label,code,reason,output))
  runs.append({'label':label,'compiler_exit':code,'object_sha256':H(obj),'source_sha256':H(src),'seed_sha256':seedhash,'log_sha256':H(log),'stdout':output,'sampled_peak_rss_bytes':peak,'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'command':cmd})
  print(label,'exit',code,'peak_RSS',peak,flush=True)
 if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['stdout']!=runs[1]['stdout']:raise ValueError('sibling mismatch')
 after=verify()
 if before!=after or H(__file__)!=driver:raise ValueError('audit or driver drift')
 receipt={'status':'PASS_PAIRED_FREEJ_MAIN_INDEX_UNIQUE','runs':runs,'parent_audit':after,'driver_sha256':driver,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Conditional all-model uniqueness of the main ordinate index; no compact44 port calibration, checker, machine, or iPRA proof. Inherited provider axiom inventory and package-transitive/dynamic limitations remain; monitoring is sampled and --deps has a leader timeout.'}
 with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_PAIRED_FREEJ_MAIN_INDEX_UNIQUE',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
