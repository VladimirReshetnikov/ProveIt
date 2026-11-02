#!/usr/bin/env python3
"""Paired exact compact coefficient-mass check over the audited 943-row provider."""
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:
 raise RuntimeError('invoke with python3 -I -S, without optimization')
HERE=Path(__file__).resolve().parent;BASE=HERE.parent;ROOT=HERE.parents[2]
SOURCE=HERE/'CompactCoefficientMass.lean'; AUDIT=ROOT/'reviews/compact44-943-table-independent-audit'
TABLE=BASE/'compact44-943-table-prototype'; PREFIX=Path('/tmp/ipra-thirteen-parent-window-pair-01'); PARENT=Path('/tmp/ipra-compact943-table-pair-01')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'; LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'ca20b0796cbdd1b6c86e6032998fec7d5577b0f775b88d8395db349c7b1b2e6e',
 AUDIT/'audit.py':'9d479abf187a75f6e7e6338ac6e86a37583afd4ca9e7a5c8ca8bcf51b36facc9',
 AUDIT/'CHECK.json':'a4efb0c47a97e78497915c891b0d76be82dc8753eb842c2d15a921f3568ff920',
 AUDIT/'terminal-observation.json':'4e25b7bc5f86ad810fbde036598fe01a6b817502f6760c3042eef189357524f7',
 TABLE/'evidence/receipt.json':'d2b5c30ae68b12c502e7621ef4a26840bb25ce9d9865a5b1fd8d9c4be3625650',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
EXPECTED="""'CompactCoefficientMass.values_in_range' depends on axioms: [propext]
'CompactCoefficientMass.selector_mass_exact' depends on axioms: [propext]
'CompactCoefficientMass.copy_mass_exact' depends on axioms: [propext]
'CompactCoefficientMass.coefficient_mass_exact' depends on axioms: [propext]
'CompactCoefficientMass.stencil_mass_exact' depends on axioms: [propext]
'CompactCoefficientMass.triple_stencil_below_half' depends on axioms: [propext]
'CompactCoefficientMass.predecessor_slack' depends on axioms: [propext]
'CompactCoefficientMass.heterogeneous_mass_slack' depends on axioms: [propext]
"""
def verify():
 for p,h in PINS.items():
  if H(p)!=h:raise ValueError(('input drift',str(p)))
 obs=json.loads((AUDIT/'terminal-observation.json').read_text());audit=json.loads((AUDIT/'CHECK.json').read_text())
 if obs['observed_exit'] or obs['receipt_sha256']!=PINS[AUDIT/'CHECK.json'] or audit['status']!='PASS_INDEPENDENT_COMPACT44_943_TABLE_AUDIT':raise ValueError('parent audit observation')
 cmd=[sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')];p=subprocess.run(cmd,capture_output=True,text=True,timeout=600)
 if p.returncode or p.stderr:raise ValueError(('parent audit rerun',p.returncode,p.stdout,p.stderr))
 if json.loads(p.stdout)!=audit:raise ValueError('parent audit output drift')
 return audit

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
 if out.parent.resolve()!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-coefficient-mass-pair-') or os.path.lexists(out):raise ValueError('need fresh dedicated /tmp output')
 driver=H(__file__);before=verify();spec=importlib.util.spec_from_file_location('monitor',MONITOR);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
 out.mkdir();runs=[];parent=json.loads((TABLE/'evidence/receipt.json').read_text())
 for label in ('author','peer'):
  run=out/label;root=run/'src';root.mkdir(parents=True);src=root/'CompactCoefficientMass.lean';shutil.copyfile(SOURCE,src);lib=run/'lib';monitor.overlay(PREFIX/label/'lib',lib)
  target=lib/'DiophantineConsistency/Compact943Data.olean';seed=PARENT/label/'Compact943Data.olean';pr=next(r for r in parent['runs'] if r['label']==label)
  if os.path.lexists(target) or H(seed)!=pr['object_sha256']:raise ValueError('parent object mismatch or collision')
  shutil.copyfile(seed,target);seedhash=H(target);env=os.environ.copy()
  for k in tuple(env):
   if k.startswith('PYTHON') or k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT','LEAN_SRC_PATH','LEAN_SYSROOT'):env.pop(k,None)
  env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120)
  expected={str(PACKAGE/'Init.olean'),str(target)}
  if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('deps',deps.returncode,deps.stdout,deps.stderr))
  obj=run/'CompactCoefficientMass.olean';log=run/'compiler.log';cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
  code,peak,reason=monitor.monitored(cmd,env,log);output=log.read_text()
  if code or reason or output!=EXPECTED or not obj.is_file() or H(src)!=PINS[SOURCE] or H(target)!=seedhash:raise ValueError(('compiler/result mismatch',label,code,reason,output))
  runs.append({'label':label,'compiler_exit':code,'object_sha256':H(obj),'source_sha256':H(src),'seed_sha256':seedhash,'log_sha256':H(log),'stdout':output,'sampled_peak_rss_bytes':peak,'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'command':cmd})
  print(label,'exit',code,'peak_RSS',peak,flush=True)
 if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['stdout']!=runs[1]['stdout']:raise ValueError('sibling mismatch')
 after=verify()
 if before!=after or H(__file__)!=driver:raise ValueError('audit or driver drift')
 receipt={'status':'PASS_PAIRED_COMPACT_COEFFICIENT_MASS','runs':runs,'parent_audit':after,'driver_sha256':driver,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Finite selector and copy coefficient-mass evaluation and half-radix inequality for the retained Lean table; not an all-model graph-to-carry application, port binding, arbitrary-model simulation or iPRA bridge. Inherited provider axiom inventory and package-transitive/dynamic limitations remain; monitoring is sampled and --deps has a leader timeout.'}
 with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_PAIRED_COMPACT_COEFFICIENT_MASS',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
