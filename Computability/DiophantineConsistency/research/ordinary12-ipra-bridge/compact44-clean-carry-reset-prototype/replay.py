#!/usr/bin/env python3
"""Source-frozen paired conditional clean-predecessor carry-reset client."""
import argparse,hashlib,importlib.util,json,os,shutil,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S, without optimization')
HERE=Path(__file__).resolve().parent;BASE=HERE.parent;ROOT=HERE.parents[2]
PLAN=BASE/'compact44-clean-carry-closure-plan';AUDIT=ROOT/'reviews/compact44-heterogeneous-carry-independent-audit'
PLAN_AUDIT=ROOT/'reviews/compact44-clean-carry-closure-independent-audit/CHECK.json'
PREFIX=Path('/tmp/ipra-compact-heterogeneous-carry-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');SOURCE=HERE/'CompactCarryReset.lean'
PINS={MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 PLAN/'scan.py':'9f7387fec07bfb7d349c5f4185ef4522b094c60e4e426afeb3c14532aec27a5e',PLAN/'scan.json':'46003ec1b3b092c2044f61ddb0811b4e11230b9d505d7c580b764aeb1343bfae',PLAN/'README.md':'518fad1d974867c2c96c17f7d4fd02f88b061beb05fcab8139288a5154269860',
 AUDIT/'audit.py':'679185715d3b64bea7bf7f5558d94720a5ba2c2588127ddd0c01e31c40868d0d',AUDIT/'CHECK.json':'415d5b4056e35eda01b7896c330d9298af4a410fffca31edad12fe902afd11f9',AUDIT/'terminal-observation.json':'d968e82ed55952507e44d45bfc60d6f5bcb871966529547849c32efb005ab5c1',
 PLAN_AUDIT:'83d865857f0eb2e42509e99c6cf646e4f10ebb296a5daeb1cfa4fd32687dc0f3',PLAN_AUDIT.parent/'terminal-observation.json':'17b9ac6f101f91a46e562aa52af154feef0f16e370b17e6c2a7677018c933b87',SOURCE:'f80d473cb579a24086ae29e560cce33a8ed282bf90ce7458302ec8a3d244928d'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
EXPECTED="'CompactCarryReset.digit_after_bounded_predecessor' depends on axioms: [propext, Classical.choice, Quot.sound]\n'CompactCarryReset.clean_after_bounded_predecessor' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require_init(package):
 p=package/'Init.olean'
 if not p.is_file():raise ValueError(('required Init object missing',str(p)))
 return str(p)
def require_output(obj):
 if not obj.is_file() or obj.is_symlink():raise ValueError(('invalid output object',str(obj)))
def output_guards(obj, *, before):
 stem=str(obj)[:-len('.olean')];observed=guard(stem)
 for suffix in SUFFIXES:
  value=observed[stem+suffix]
  if suffix=='.olean' and not before:
   if value is None or obj.is_symlink():raise ValueError(('missing or symlink output',str(obj)))
  elif value is not None:raise ValueError(('unexpected output companion',stem+suffix))
 return observed

def check_source(src):
 if not src.is_file() or src.is_symlink() or H(src)!=PINS[SOURCE]:raise ValueError(('frozen source drift',str(src)))
def guard(stem):
 result={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):
   if not p.is_file():raise ValueError(('invalid companion',str(p)))
   result[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)}
  else:result[str(p)]=None
 return result
def checkguards(guards):
 for name,prior in guards.items():
  p=Path(name)
  if prior is None:
   if os.path.lexists(p):raise ValueError(('unexpected companion',name))
  elif not p.is_file() or str(p.resolve())!=prior['realpath'] or H(p)!=prior['sha256']:raise ValueError(('companion drift',name))
def mergeguards(allguards,new):
 for key,value in new.items():
  if key in allguards and allguards[key]!=value:raise ValueError(('guard changed between steps',key))
  allguards[key]=value
def validate_output(text):
 if text!=EXPECTED:raise ValueError('unexpected compiler output')

def require_no_seed_companions(seedguards,seed,label):
 if any(value is not None for path,value in seedguards.items() if path!=str(seed)):raise ValueError(('unexpected parent seed companion',label))

def load(path):
 spec=importlib.util.spec_from_file_location('monitor',path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj
def verify():
 for p,h in PINS.items():
  if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
 scan=json.loads((PLAN/'scan.json').read_text());parent=json.loads((AUDIT/'CHECK.json').read_text());obs=json.loads((AUDIT/'terminal-observation.json').read_text());closure=json.loads(PLAN_AUDIT.read_text());cobs=json.loads((PLAN_AUDIT.parent/'terminal-observation.json').read_text())
 if scan['status']!='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD' or len(scan['inherited_objects'])!=115 or len(scan['seeds'])!=2:raise ValueError('invalid closure scan')
 if parent.get('status')!='PASS_INDEPENDENT_COMPACT44_HETEROGENEOUS_CARRY_AUDIT' or type(parent.get('recorded_outer_exit')) is not int or parent['recorded_outer_exit']!=0 or type(obs.get('observed_exit')) is not int or obs['observed_exit']!=0 or type(obs.get('lean_compilations_started')) is not int or obs['lean_compilations_started']!=0 or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json']:raise ValueError('invalid parent observation')
 if closure.get('status')!='PASS_INDEPENDENT_CLEAN_CARRY_SOURCE_CLOSURE' or closure.get('inherited_objects_per_side')!=115 or type(cobs.get('observed_exit')) is not int or cobs['observed_exit']!=0 or cobs.get('lean_launched') is not False or cobs.get('check_sha256')!=PINS[PLAN_AUDIT]:raise ValueError('invalid closure review')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,text=True,timeout=120)
 if q.returncode or q.stderr or json.loads(q.stdout)!=scan:raise ValueError(('source closure drift',q.returncode,q.stderr))
 q=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,text=True,timeout=1200)
 if q.returncode or q.stderr or json.loads(q.stdout)!=parent:raise ValueError(('parent audit rerun failed',q.returncode,q.stderr))
 return scan,parent
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
 if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-clean-carry-pair-') or out.exists() or out.is_symlink():raise ValueError('use a fresh direct /tmp/ipra-compact-clean-carry-pair-* path')
 driver=H(__file__);scan,parent=verify();monitor=load(MONITOR);out.mkdir();frozen=out/'frozen/DiophantineConsistency';frozen.mkdir(parents=True);src=frozen/'CompactCarryReset.lean';shutil.copyfile(SOURCE,src);check_source(src);runs=[];allguards={}
 for label in ('author','peer'):
  check_source(src);run=out/label;run.mkdir();lib=run/'lib';monitor.overlay(PREFIX/label/'lib',lib)
  item=next(x for x in scan['seeds'] if x['side']==label);seed=Path(item['source']);target=lib/item['target_relative_path'];target.parent.mkdir(parents=True,exist_ok=True)
  for suffix in SUFFIXES:
   if os.path.lexists(Path(str(target)[:-6]+suffix)):raise ValueError(('seed target collision',label,suffix))
  if not seed.is_file() or H(seed)!=item['sha256']:raise ValueError(('parent seed drift',label))
  seedguards=guard(str(seed)[:-6]);checkguards(seedguards)
  require_no_seed_companions(seedguards,seed,label)
  mergeguards(allguards,seedguards)
  shutil.copyfile(seed,target)
  if not target.is_file() or target.is_symlink() or H(target)!=item['sha256']:raise ValueError(('seed copy drift',label))
  expected={require_init(PACKAGE),str(target)};guards={}
  for item in expected:guards.update(guard(item[:-6]))
  checkguards(allguards);checkguards(guards);mergeguards(allguards,guards)
  env=os.environ.copy()
  for key in tuple(env):
   if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
  env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
  if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('direct imports differ',label,deps.returncode,deps.stdout,deps.stderr))
  checkguards(allguards);check_source(src);obj=lib/'DiophantineConsistency/CompactCarryReset.olean';log=run/'compiler.log'
  output_guards(obj,before=True)
  cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={out/"frozen"}',str(src),'-o',str(obj)]
  code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text()
  if code or reason:raise ValueError(('compiler failure',label,code,reason,text[-8000:]))
  validate_output(text);require_output(obj);checkguards(allguards);mergeguards(allguards,output_guards(obj,before=False));check_source(src)
  runs.append({'label':label,'compiler_exit':code,'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'command':cmd,'source_sha256':H(src),'object_sha256':H(obj),'log_sha256':H(log),'stdout':text,'sampled_peak_rss_bytes':peak,'stop_reason':reason})
  print(label,'exit',code,'peak_RSS',peak,flush=True)
 if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['stdout']!=runs[1]['stdout']:raise ValueError('paired output differs')
 check_source(src);checkguards(allguards);scan2,parent2=verify();check_source(src);checkguards(allguards)
 if scan2!=scan or parent2!=parent or H(__file__)!=driver:raise ValueError('parent inputs or driver changed')
 receipt={'status':'PASS_PAIRED_COMPACT_CLEAN_CARRY_RESET','runs':runs,'driver_sha256':driver,'direct_and_output_guards':allguards,'parent_audit':parent,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Conditional IΣ₁ clean-predecessor carry reset for externally finite families, with explicit CarryInput, predecessor, slack and radix premises; no graph/fractional-rotation instantiation, checker, machine or PRA proof. Point-in-time guard, sampled resource and inherited provider/package limits.'}
 with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_PAIRED_COMPACT_CLEAN_CARRY_RESET',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
