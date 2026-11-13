#!/usr/bin/env python3
"""Source-frozen paired six-module fixed-symbolic graph-digit client rebuild."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S, without optimization')
HERE=Path(__file__).resolve().parent; BASE=HERE.parent; ROOT=HERE.parents[2]
PLAN=BASE/'compact44-fixed-graph-closure-plan'; AUDIT=ROOT/'reviews/compact44-symbolic-graph-join-independent-audit'
PLAN_AUDIT=ROOT/'reviews/compact44-fixed-graph-closure-independent-audit/CHECK.json'
PREFIX=Path('/tmp/ipra-compact-symbolic-graph-join-pair-01'); PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'; LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SOURCES=()
PINS={MONITOR: '2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 PLAN/'scan.json': 'f7992ebc4b0c20aa44fb01bbd7ac89b304e657a2556142992ed1594aea5f514b',
 PLAN/'scan.py': '0c0332f9558eb571ce6a8f237321e5522fa79a554fe7ea4b67321fcea212184c',
 PLAN/'README.md': '9e08ab056c4f2ac8893eb0c802015e48751382f7bd76ccadc26b149dd01ad330',
 AUDIT/'audit.py': '26fcfbc12c464b17aa8e67166c6d86a40dba87259cd66c1602dc90da48e08488',
 AUDIT/'CHECK.json': '3164ef421742c093b07fb1ff491c19d9586f2ff19f83d2371f3311b4958721ec',
 AUDIT/'terminal-observation.json': '6b711fb6bbe5152cde880320b73bf928984a993aebcf46c2002eb62a99ab0ab8',
 PLAN_AUDIT: '363986d2a3575920a4fcd069560aef98b1a8ad0eb23fa46af58f0fc222e8af9f',
 PLAN_AUDIT.parent/'terminal-observation.json':'ab07605d84f0b659cceb438148e1cd564059cf0d8412a090b3b1f8cdffe3069c'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def validate_reports(name,reports):
 expected_reports={
  'CompactMaskBounds': {'bounds_of_residues'},
  'CompactBetaResidues': {'residues'},
  'CompactMaskBoundFinish': {'bounds'},
  'CompactFixedBeta': {'beta_identity_generic','beta_identity','bounds'},
  'CompactSymbolicPorts': {'graph_digits_of_symbols','graph_digits'},
  'CompactGenericGraphDigits': {'graph_digits','fixed_graph_digits'}}
 stem=name.rsplit('.',1)[-1]
 expected_reports={stem+'.'+n for n in expected_reports.get(stem,set())}
 if len(reports)!=len(expected_reports) or {report for report,_ in reports}!=expected_reports or any({x.strip() for x in ax.split(',') if x.strip()} != {'propext','Classical.choice','Quot.sound'} for report,ax in reports):raise ValueError(('unexpected axiom report',name,reports))

def require_init(package):
 init=package/'Init.olean'
 if not init.is_file():raise ValueError(('required Init object missing',str(init)))
 return str(init)

def load(path):
 spec=importlib.util.spec_from_file_location('monitor',path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def verify():
 for p,h in PINS.items():
  if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
 scan=json.loads((PLAN/'scan.json').read_text());review=json.loads((AUDIT/'CHECK.json').read_text());obs=json.loads((AUDIT/'terminal-observation.json').read_text());plan_review=json.loads(PLAN_AUDIT.read_text());plan_obs=json.loads((PLAN_AUDIT.parent/'terminal-observation.json').read_text())
 if scan['status']!='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD' or len(scan['modules'])!=6 or len(scan['inherited_objects'])!=134:raise ValueError('invalid scan')
 if review.get('status')!='PASS_INDEPENDENT_SYMBOLIC_GRAPH_JOIN_PAIR_AUDIT' or review.get('recorded_outer_exit')!=0 or obs.get('independent_review_exit')!=0 or obs.get('check_sha256')!=PINS[AUDIT/'CHECK.json']:raise ValueError('invalid graph-digit audit')
 if plan_review.get('status')!='PASS_INDEPENDENT_POINT_IN_TIME_FIXED_GRAPH_CLOSURE' or plan_review.get('parent_object_count_each')!=134 or plan_review.get('ordered_sources')!=[x['module'] for x in scan['modules']] or plan_obs.get('observed_exit')!=0 or plan_obs.get('receipt_sha256')!=PINS[PLAN_AUDIT]:raise ValueError('invalid closure audit')
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,text=True,timeout=120)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=scan:raise ValueError(('source closure drift',proc.returncode,proc.stderr))
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,text=True,timeout=900)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=review:raise ValueError(('graph-digit audit rerun failed',proc.returncode,proc.stderr))
 return scan,review

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
 if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-fixed-graph-digits-pair-') or out.exists() or out.is_symlink():raise ValueError('use a fresh direct /tmp/ipra-compact-fixed-graph-digits-pair-* path')
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
 runs=[]
 for label in ('author','peer'):
  run=out/label;run.mkdir();lib=run/'lib';monitor.overlay(PREFIX/label/'lib',lib)
  env=os.environ.copy()
  for key in tuple(env):
   if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
  env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);steps=[]
  for name,src,digest,imports in rows:
   rel=Path(*name.split('.'));obj=(lib/rel).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=run/(name.replace('.','_')+'.log')
   if obj.exists() or obj.is_symlink():raise ValueError(('output path occupied',label,name))
   cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={frozen}',str(src),'-o',str(obj)]
   code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text();reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
   if code or reason or 'warning:' in text or 'error:' in text or 'sorryAx' in text:raise ValueError(('compiler failure',label,name,code,reason,text[-8000:]))
   validate_reports(name,reports)
   deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60);expected={require_init(PACKAGE)}
   for dep in imports:
    rel=Path(*dep.split('.')).with_suffix('.olean');candidate=lib/rel
    if not candidate.is_file() and dep.startswith('DiophantineConsistency.'):
     raise ValueError(('project import absent from same-side overlay',name,dep))
    if not candidate.is_file():candidate=PACKAGE/rel
    if not candidate.is_file():raise ValueError(('missing imported object',name,dep))
    expected.add(str(candidate))
   if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('direct imports differ',label,name,deps.returncode,deps.stdout,deps.stderr))
   if H(src)!=digest:raise ValueError(('frozen source drift',name))
   steps.append({'module':name,'compiler_exit':code,'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'command':cmd,'source_sha256':digest,'object_sha256':H(obj),'log_sha256':H(log),'stdout':text,'axiom_reports':reports,'sampled_peak_rss_bytes':peak,'stop_reason':reason})
   print(label,name,'exit',code,'peak_RSS',peak,flush=True)
  runs.append({'label':label,'steps':steps})
 if [{k:v for k,v in r.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')} for r in runs[0]['steps']]!=[{k:v for k,v in r.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')} for r in runs[1]['steps']]:raise ValueError('paired outputs differ')
 scan2,review2=verify()
 if scan2!=scan or review2!=review or H(__file__)!=driver:raise ValueError('parent inputs or driver changed')
 receipt={'status':'PASS_PAIRED_COMPACT_FIXED_GRAPH_DIGITS','runs':runs,'driver_sha256':driver,'graph_digit_audit':review,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Fixed-symbolic graph digit bounds, with arbitrary K and explicit graph-zero, positivity, radix and repunit assumptions. No retained-port binding, checker, machine simulation or PRA proof. No full package/dynamic ancestry audit.'}
 with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_PAIRED_COMPACT_FIXED_GRAPH_DIGITS',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
