#!/usr/bin/env python3
"""Source-frozen paired 12-module free-J concrete-digit client rebuild."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent; BASE=HERE.parent; ROOT=HERE.parents[2]
PLAN=BASE/'free-j-concrete-digits-closure-plan'; AUDIT=ROOT/'reviews/ordinary12-freej-saturation-client-independent-audit'
PLAN_AUDIT=ROOT/'reviews/ordinary12-freej-concrete-digits-closure-independent-audit/CHECK.json'
PREFIX=Path('/tmp/ipra-freej-saturation-client-pair-01'); PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'; LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SOURCES=(HERE/'FreeJConcreteDigitsClient.lean',)
PINS={MONITOR: '2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 PLAN/'scan.json': '0f7dd9d99db1473c92fa9637560c2aabf78f5898ad74154418bf07ed9d78db8a',
 PLAN/'scan.py': '81c1b02704a384f039bfc122d2248fc40ea24007abd85a33ea0385609010016a',
 PLAN/'README.md': '9ba8e70853fd86fd2417fd227ff7fa1ea2cb55f310274d70df18970aba64b4c4',
 AUDIT/'audit.py': '73fec589e911a9597cf3233c8063693ea741e395e6e6de851e470ffef25a1a39',
 AUDIT/'CHECK.json': '847f3e467e93d871087695ee3c66f8042c22767a7d43ec1a14973cffe6ee043f',
 AUDIT/'terminal-observation.json': 'f918d6e6ce70bf660ff9140c5fefed179c74c7902a64ecd70b20cfd27366faff',
 PLAN_AUDIT: '47bd9296128571350c0d4f54d7cb0940206b1e6c96a7b8e4cbb2dd4cddbd9191',
 SOURCES[0]: 'e859356894c307fffaf349ca65d6a0b40478201c95571d5b660f099816a2f52d'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(path):
 spec=importlib.util.spec_from_file_location('monitor',path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def verify():
 for p,h in PINS.items():
  if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
 scan=json.loads((PLAN/'scan.json').read_text());review=json.loads((AUDIT/'CHECK.json').read_text());obs=json.loads((AUDIT/'terminal-observation.json').read_text());plan_review=json.loads(PLAN_AUDIT.read_text())
 if scan['status']!='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD' or len(scan['modules'])!=12 or len(scan['inherited_objects'])!=114:raise ValueError('invalid scan')
 if review.get('status')!='PASS_INDEPENDENT_FREEJ_SATURATION_CLIENT_AUDIT' or review.get('recorded_outer_exit')!=0 or obs.get('observed_exit')!=0 or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json']:raise ValueError('invalid saturation audit')
 if plan_review.get('status')!='PASS_INDEPENDENT_FREEJ_CONCRETE_DIGITS_SOURCE_CLOSURE_AUDIT' or plan_review.get('normal_scan_exit')!=0 or plan_review.get('inherited_objects_per_side')!=114:raise ValueError('invalid closure audit')
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,text=True,timeout=120)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=scan:raise ValueError(('source closure drift',proc.returncode,proc.stderr))
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,text=True,timeout=900)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=review:raise ValueError(('saturation audit rerun failed',proc.returncode,proc.stderr))
 return scan,review

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
 if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-freej-concrete-digits-client-pair-') or out.exists() or out.is_symlink():raise ValueError('use a fresh direct /tmp/ipra-freej-concrete-digits-client-pair-* path')
 scan,review=verify(); monitor=load(MONITOR);out.mkdir(); frozen=out/'frozen';frozen.mkdir();rows=[]
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
   expected_reports={
    'CompactListMask': {'model_mask_origin','model_mask_lt','model_mask_class','digits_add_defect'},
    'CompactConcreteMask': {'concrete_bit_recipe','model_class','model_lt','model_origin','concrete_recipe'},
    'CompactDummyBound': {'forbidden_zero','ordinary_le_one','dummy_le_three'},
    'CompactMaskSlot': {'ordinary_at','forbidden_at','dummy_at'},
    'CompactMixedIncrement': {'decode_mixed_increment'},
    'CompactConcreteIncrement': {'recipe_digits','mask_eq_bit_recipe'},
    'FreeJConcreteDigitsClient': {'graph_digits'}}
   stem=name.rsplit('.',1)[-1]
   expected_reports={stem+'.'+n for n in expected_reports.get(stem,set())}
   if len(reports)!=len(expected_reports) or {report for report,_ in reports}!=expected_reports or any({x.strip() for x in ax.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for _,ax in reports):raise ValueError(('unexpected axiom report',name,reports))
   deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60);expected={str(PACKAGE/'Init.olean')}
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
 if scan2!=scan or review2!=review:raise ValueError('parent inputs changed')
 receipt={'status':'PASS_PAIRED_FREEJ_CONCRETE_DIGITS_CLIENT','runs':runs,'saturation_audit':review,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Conditional graph digit bounds with explicit graph, beta, radix, population and symbolic low-port equality assumptions. No retained MC binding, checker, machine simulation or PRA proof. No full package/dynamic ancestry audit.'}
 with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_PAIRED_FREEJ_CONCRETE_DIGITS_CLIENT',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
