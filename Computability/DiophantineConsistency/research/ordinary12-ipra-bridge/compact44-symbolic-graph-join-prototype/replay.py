#!/usr/bin/env python3
"""Source-frozen paired seven-module symbolic-mask graph-digit client rebuild."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S, without optimization')
HERE=Path(__file__).resolve().parent; BASE=HERE.parent; ROOT=HERE.parents[2]
PLAN=BASE/'compact44-symbolic-graph-closure-plan'; AUDIT=ROOT/'reviews/ordinary12-freej-concrete-digits-client-independent-audit'
PLAN_AUDIT=ROOT/'reviews/compact44-symbolic-graph-closure-independent-audit/CHECK.json'
LOW_AUDIT=ROOT/'reviews/compact44-low-even-independent-audit'
PREFIX=Path('/tmp/ipra-freej-concrete-digits-client-pair-01'); PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'; LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SOURCES=()
PINS={MONITOR: '2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 PLAN/'scan.json': 'd98d3134991ab4e5238d9d3ac0354c0ab7f4dd9d3a4dce8b1fbd407c61ad3a2b',
 PLAN/'scan.py': '44aedeca22e72113196d9e733f5bd6ad39b260910f21e8be148cd5e310fccacb',
 PLAN/'README.md': '37e79b1fc802e2b114f3dff2484fa843261929f1bf44abd41bc30007ec90cd6a',
 AUDIT/'audit.py': 'c17f8d20b18f18cfb89200229a2233f4084e6d5735a9001c8a41352f3239fb40',
 AUDIT/'CHECK.json': '5ef4ae700c1105220472fe57952929071a6c5666d1cad01a3b37c971c49d3056',
 AUDIT/'terminal-observation.json': '11434c5c2368518a75264e68ee27784ab93162e1c39a56e34df18c10b8b5b2d6',
 PLAN_AUDIT: '05de5c689e16dab9c5ec0cf5a319f81c4d2d96ceeebfe7503ee163622686bc2b',
 PLAN_AUDIT.parent/'terminal-observation.json':'28f97011af2a1c64e42f8af0396edd1bffa7f033a73de3509b6f013bbb866ffa',
 LOW_AUDIT/'audit.py':'977a0c8fe03c2e393c2234ad8ecaf8170fef4c0203ec9a076a3606ee9b880042',
 LOW_AUDIT/'CHECK.json':'5ddfb822587813f5883fc32ec2ced206f913ac362f35a762e1cee9b8503f395d',
 LOW_AUDIT/'terminal-observation.json':'6ee553dd579a8ba61323c2de04bad503d7f8f9294ec183e7367dae844b938529'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def validate_reports(name,reports):
 expected_reports={
  'CompactLowPopulation': {'list_population','model_population'},
  'CompactSupportCard': {'support_card'},
  'CompactLowExact': {'model_population'},
  'CompactLowEven': {'low_even'},
  'CompactHighPopulation': {'model_population','model_lt'},
  'CompactHighResidue': {'natural_mod_eight','model_mod_eight'},
  'CompactSymbolicGraphDigits': {'graph_digits'}}
 stem=name.rsplit('.',1)[-1]
 expected_reports={stem+'.'+n for n in expected_reports.get(stem,set())}
 if len(reports)!=len(expected_reports) or {report for report,_ in reports}!=expected_reports or any({x.strip() for x in ax.split(',') if x.strip()} != ({'propext'} if report=='CompactHighResidue.natural_mod_eight' else {'propext','Classical.choice','Quot.sound'}) for report,ax in reports):raise ValueError(('unexpected axiom report',name,reports))

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
 if scan['status']!='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD' or len(scan['modules'])!=7 or len(scan['inherited_objects'])!=127:raise ValueError('invalid scan')
 if review.get('status')!='PASS_INDEPENDENT_FREEJ_CONCRETE_DIGITS_CLIENT_AUDIT' or review.get('recorded_outer_exit')!=0 or obs.get('successful_review_exit')!=0 or obs.get('check_sha256')!=PINS[AUDIT/'CHECK.json']:raise ValueError('invalid graph-digit audit')
 if plan_review.get('status')!='PASS_INDEPENDENT_SYMBOLIC_GRAPH_SOURCE_CLOSURE_AUDIT' or plan_review.get('fresh_scan_exit')!=0 or plan_review.get('inherited_objects_per_side')!=127 or plan_obs.get('observed_exit')!=0 or plan_obs.get('check_sha256')!=PINS[PLAN_AUDIT]:raise ValueError('invalid closure audit')
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,text=True,timeout=120)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=scan:raise ValueError(('source closure drift',proc.returncode,proc.stderr))
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,text=True,timeout=900)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=review:raise ValueError(('graph-digit audit rerun failed',proc.returncode,proc.stderr))
 low=json.loads((LOW_AUDIT/'CHECK.json').read_text());low_obs=json.loads((LOW_AUDIT/'terminal-observation.json').read_text())
 if low.get('status')!='PASS_INDEPENDENT_COMPACT44_LOW_EVEN_AUDIT' or low.get('recorded_outer_exit')!=0 or low_obs.get('independent_review_exit')!=0 or low_obs.get('check_sha256')!=PINS[LOW_AUDIT/'CHECK.json']:raise ValueError('invalid low-even audit')
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(LOW_AUDIT/'audit.py')],capture_output=True,text=True,timeout=1800)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=low:raise ValueError(('low-even audit rerun failed',proc.returncode,proc.stderr))
 return scan,review,low

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
 if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-symbolic-graph-join-pair-') or out.exists() or out.is_symlink():raise ValueError('use a fresh direct /tmp/ipra-compact-symbolic-graph-join-pair-* path')
 driver=H(__file__);scan,review,low=verify(); monitor=load(MONITOR);out.mkdir(); frozen=out/'frozen';frozen.mkdir();rows=[]
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
 scan2,review2,low2=verify()
 if scan2!=scan or review2!=review or low2!=low or H(__file__)!=driver:raise ValueError('parent inputs or driver changed')
 receipt={'status':'PASS_PAIRED_COMPACT_SYMBOLIC_GRAPH_JOIN','runs':runs,'driver_sha256':driver,'graph_digit_audit':review,'low_even_audit':low,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Conditional graph digit bounds with explicit low- and high-symbolic-port equalities, graph, beta, radix, split and product assumptions. No retained-port binding, checker, machine simulation or PRA proof. No full package/dynamic ancestry audit.'}
 with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_PAIRED_COMPACT_SYMBOLIC_GRAPH_JOIN',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
