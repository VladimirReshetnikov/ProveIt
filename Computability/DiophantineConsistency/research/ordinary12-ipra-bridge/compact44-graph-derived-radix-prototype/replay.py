#!/usr/bin/env python3
"""Source-frozen paired three-module graph-derived symbolic radix rebuild."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S, without optimization')
HERE=Path(__file__).resolve().parent; BASE=HERE.parent; ROOT=HERE.parents[2]
PLAN=BASE/'compact44-graph-derived-radix-closure-plan'; AUDIT=ROOT/'reviews/compact44-fixed-graph-independent-audit'
PLAN_AUDIT=ROOT/'reviews/compact44-graph-radix-closure-independent-audit/CHECK.json'
PREFIX=Path('/tmp/ipra-compact-fixed-graph-digits-pair-01'); PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'; LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SOURCES=()
PINS={MONITOR: '2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 PLAN/'scan.json': 'd29382e32a7c9514fe9284287ac23621139dfc876a30fb50ed62fd27cc16aa61',
 PLAN/'scan.py': '1326c3870b9a4b7be54fffe6388d19b6e8073510d1ebe9b29ebf64f46747880b',
 PLAN/'README.md': 'd9aa7e9912c3f8603bf99d14998cb37b7b0ea64861b5ef2862e1c43b9cc91ad5',
 AUDIT/'audit.py': '9691c9dd8973f6417ea9b54383c3c3bf5c2d008d6ab7551a0f44825bda8c5199',
 AUDIT/'CHECK.json': '3d380723c818d4f16dc78e5c942b5e3cab8f7a01cf8a5bfad47ad3af3941abc1',
 AUDIT/'terminal-observation.json': '57644d3589a4d0b0f88f724f1bb026a3104b5df58704edba233f7e5072d56120',
 PLAN_AUDIT: '43f29a866dd7c4b18acd6bc2dfe1de0a392ab4bd01d1554b778d4c700954bd84',
 PLAN_AUDIT.parent/'terminal-observation.json':'05d39d2af2c12591059533a0c7204d06530aa163f53b9a8b3d255e9668a51379'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def validate_reports(name,reports):
 expected_reports={
  'FreeJPowerCancel': {'graph_divides_power'},
  'FreeJRadixAlignment': {'graph_alignment'},
  'CompactGraphDerivedRadix': {'graph_digits','fixed_graph_digits'}}
 stem=name.rsplit('.',1)[-1]
 expected_reports={stem+'.'+n for n in expected_reports.get(stem,set())}
 if len(reports)!=len(expected_reports) or {report for report,_ in reports}!=expected_reports or any({x.strip() for x in ax.split(',') if x.strip()} != {'propext','Classical.choice','Quot.sound'} for report,ax in reports):raise ValueError(('unexpected axiom report',name,reports))

def require_init(package):
 init=package/'Init.olean'
 if not init.is_file():raise ValueError(('required Init object missing',str(init)))
 return str(init)

SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
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
  elif not p.is_file() or str(p.resolve())!=prior['realpath'] or H(p)!=prior['sha256']:
   raise ValueError(('companion drift',name))

def mergeguards(allguards,new):
 for key,value in new.items():
  if key in allguards and allguards[key]!=value:raise ValueError(('guard changed between steps',key))
  allguards[key]=value

def check_frozen(rows):
 for name,src,digest,_ in rows:
  if not src.is_file() or src.is_symlink() or H(src)!=digest:raise ValueError(('frozen source drift',name))

def require_output(obj):
 if not obj.is_file() or obj.is_symlink():raise ValueError(('invalid output object',str(obj)))

def load(path):
 spec=importlib.util.spec_from_file_location('monitor',path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def verify():
 for p,h in PINS.items():
  if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
 scan=json.loads((PLAN/'scan.json').read_text());review=json.loads((AUDIT/'CHECK.json').read_text());obs=json.loads((AUDIT/'terminal-observation.json').read_text());plan_review=json.loads(PLAN_AUDIT.read_text());plan_obs=json.loads((PLAN_AUDIT.parent/'terminal-observation.json').read_text())
 if scan['status']!='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD' or len(scan['modules'])!=3 or len(scan['inherited_objects'])!=140:raise ValueError('invalid scan')
 if review.get('status')!='PASS_INDEPENDENT_COMPACT44_FIXED_GRAPH_DIGITS_AUDIT' or review.get('recorded_outer_exit')!=0 or type(obs.get('independent_review_exit')) is not int or obs['independent_review_exit']!=0 or obs.get('lean_launched') is not False or obs.get('check_sha256')!=PINS[AUDIT/'CHECK.json']:raise ValueError('invalid graph-digit audit')
 if plan_review.get('status')!='PASS_INDEPENDENT_GRAPH_RADIX_SOURCE_CLOSURE' or plan_review.get('parent_objects_per_side')!=140 or plan_review.get('ordered_sources')!=[x['module'] for x in scan['modules']] or type(plan_obs.get('observed_exit')) is not int or plan_obs['observed_exit']!=0 or plan_obs.get('lean_launched') is not False or plan_obs.get('check_sha256')!=PINS[PLAN_AUDIT]:raise ValueError('invalid closure audit')
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,text=True,timeout=120)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=scan:raise ValueError(('source closure drift',proc.returncode,proc.stderr))
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py'),review['evidence_commit'],review['receipt_sha256']],capture_output=True,text=True,timeout=1800)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=review:raise ValueError(('graph-digit audit rerun failed',proc.returncode,proc.stderr))
 return scan,review

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
 if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-graph-derived-radix-pair-') or out.exists() or out.is_symlink():raise ValueError('use a fresh direct /tmp/ipra-compact-graph-derived-radix-pair-* path')
 driver=H(__file__);scan,review=verify(); monitor=load(MONITOR);out.mkdir(); frozen=out/'frozen';frozen.mkdir();rows=[]
 for row in scan['modules']:
  src=Path(row['source']);dst=frozen/Path(*row['module'].split('.')).with_suffix('.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
  if H(dst)!=row['source_sha256']:raise ValueError(('freeze drift',row['module']))
  rows.append((row['module'],dst,row['source_sha256'],row['imports']))
 for source in SOURCES:
  dst=frozen/'DiophantineConsistency'/source.name;shutil.copyfile(source,dst)
  if H(dst)!=PINS[source]:raise ValueError(('client freeze drift',source.name))
  imports=[v for line in dst.read_text().splitlines() if line.startswith('import ') for v in line[7:].split()]
  rows.append(('DiophantineConsistency.'+source.stem,dst,PINS[source],imports))
 runs=[];allguards={}
 for label in ('author','peer'):
  run=out/label;run.mkdir();lib=run/'lib';monitor.overlay(PREFIX/label/'lib',lib)
  env=os.environ.copy()
  for key in tuple(env):
   if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
  env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);steps=[]
  for name,src,digest,imports in rows:
   check_frozen(rows)
   rel=Path(*name.split('.'));obj=(lib/rel).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=run/(name.replace('.','_')+'.log')
   for suffix in SUFFIXES:
    if os.path.lexists(Path(str(obj)[:-6]+suffix)):raise ValueError(('output companion occupied',label,name,suffix))
   expected={require_init(PACKAGE)}
   for dep in imports:
    drel=Path(*dep.split('.')).with_suffix('.olean');candidate=lib/drel
    if not candidate.is_file() and dep.startswith('DiophantineConsistency.'):
     raise ValueError(('project import absent from same-side overlay',name,dep))
    if not candidate.is_file():candidate=PACKAGE/drel
    if not candidate.is_file():raise ValueError(('missing imported object',name,dep))
    expected.add(str(candidate))
   guards={}
   for item in expected:guards.update(guard(item[:-6]))
   checkguards(allguards);checkguards(guards);mergeguards(allguards,guards)
   deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
   if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('direct imports differ',label,name,deps.returncode,deps.stdout,deps.stderr))
   checkguards(allguards)
   cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={frozen}',str(src),'-o',str(obj)]
   code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text();reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
   if code or reason or 'warning:' in text or 'error:' in text or 'sorryAx' in text:raise ValueError(('compiler failure',label,name,code,reason,text[-8000:]))
   require_output(obj);checkguards(allguards);validate_reports(name,reports)
   mergeguards(allguards,guard(str(obj)[:-6]))
   check_frozen(rows)
   steps.append({'module':name,'compiler_exit':code,'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'command':cmd,'source_sha256':digest,'object_sha256':H(obj),'log_sha256':H(log),'stdout':text,'axiom_reports':reports,'sampled_peak_rss_bytes':peak,'stop_reason':reason})
   print(label,name,'exit',code,'peak_RSS',peak,flush=True)
  runs.append({'label':label,'steps':steps})
 if [{k:v for k,v in r.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')} for r in runs[0]['steps']]!=[{k:v for k,v in r.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')} for r in runs[1]['steps']]:raise ValueError('paired outputs differ')
 check_frozen(rows);checkguards(allguards)
 scan2,review2=verify()
 check_frozen(rows);checkguards(allguards)
 if scan2!=scan or review2!=review or H(__file__)!=driver:raise ValueError('parent inputs or driver changed')
 receipt={'status':'PASS_PAIRED_COMPACT_GRAPH_DERIVED_RADIX','runs':runs,'driver_sha256':driver,'direct_and_output_guards':allguards,'graph_digit_audit':review,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Graph-derived radix, repunit and digit bounds for fixed symbolic beta/masks, with arbitrary K and explicit graph-zero and variable-positivity assumptions. No retained-port binding, checker, machine simulation or PRA proof. No full package/dynamic ancestry audit.'}
 with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_PAIRED_COMPACT_GRAPH_DERIVED_RADIX',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
