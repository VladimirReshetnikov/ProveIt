#!/usr/bin/env python3
"""Source-frozen paired four-module free-J saturation client rebuild."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent; BASE=HERE.parent; ROOT=HERE.parents[2]
PLAN=BASE/'free-j-saturation-closure-plan'; AUDIT=ROOT/'reviews/ordinary12-freej-population-client-independent-audit'
PLAN_AUDIT=ROOT/'reviews/ordinary12-freej-saturation-closure-independent-audit/CHECK.json'
PREFIX=Path('/tmp/ipra-freej-population-client-pair-02'); PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'; LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SOURCES=(HERE/'FreeJSaturationClient.lean',)
WARNING_POLICY=HERE/'warning_policy.py'
PINS={MONITOR: '2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 PLAN/'scan.json': '15b23660cec5a318e91290e1cd2b36ae540f1416fb71248f65068d619072236e',
 PLAN/'scan.py': 'cf1a513ef9e6ca1afc0afd3b8105176f9387ae01ad13e8015f0bfd217421ac59',
 PLAN/'README.md': '5a46e2d39b0d5b84fe2305b1c5ff15753d65a28c2685673f54adb5450932277a',
 AUDIT/'audit.py': '2bc61556fb4598eaac9d9754a1d6d0a13910e7678c0461a4ec15c72e30348238',
 AUDIT/'CHECK.json': '922af1e2cb645f67b7ed102e1ad6bec809f297368891f6d19f4fb59a9570c27c',
 AUDIT/'terminal-observation.json': '9345b46b37b943cc667f045e8f56c3828f108eb06b7bf7d93bcf32c30b964ed8',
 PLAN_AUDIT: 'cd4154c95a40ae6303fe564b7f765711cccbe89747b2aadd475c7c2cab2fe564',
 SOURCES[0]: 'ab822f902740442f8330068baa3a35e4392f7671ae55cfbbd271a68fcc8fcd7a',
 WARNING_POLICY: '7de66039d814425a5ea5e2f42f5459a94e31d3f0c7dd17c0728ceba9b7afba24'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(path):
 spec=importlib.util.spec_from_file_location('monitor',path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def verify():
 for p,h in PINS.items():
  if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
 scan=json.loads((PLAN/'scan.json').read_text());review=json.loads((AUDIT/'CHECK.json').read_text());obs=json.loads((AUDIT/'terminal-observation.json').read_text());plan_review=json.loads(PLAN_AUDIT.read_text())
 if scan['status']!='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD' or len(scan['modules'])!=4 or len(scan['inherited_objects'])!=109:raise ValueError('invalid scan')
 if review.get('status')!='PASS_INDEPENDENT_FREEJ_POPULATION_CLIENT_AUDIT' or review.get('recorded_outer_exit')!=0 or obs.get('observed_exit')!=0 or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json']:raise ValueError('invalid population audit')
 if plan_review.get('status')!='PASS_INDEPENDENT_FREEJ_SATURATION_SOURCE_CLOSURE_AUDIT' or plan_review.get('normal_scan_exit')!=0 or plan_review.get('inherited_objects_per_side')!=109:raise ValueError('invalid closure audit')
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,text=True,timeout=120)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=scan:raise ValueError(('source closure drift',proc.returncode,proc.stderr))
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,text=True,timeout=900)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=review:raise ValueError(('population audit rerun failed',proc.returncode,proc.stderr))
 return scan,review

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
 if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-freej-saturation-client-pair-') or out.exists() or out.is_symlink():raise ValueError('use a fresh direct /tmp/ipra-freej-saturation-client-pair-* path')
 scan,review=verify(); monitor=load(MONITOR);policy=load(WARNING_POLICY);out.mkdir(); frozen=out/'frozen';frozen.mkdir();rows=[]
 for row in scan['modules']:
  src=Path(row['source']);dst=frozen/Path(*row['module'].split('.')).with_suffix('.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
  if H(dst)!=row['source_sha256']:raise ValueError(('freeze drift',row['module']))
  rows.append((row['module'],dst,row['source_sha256'],row['imports'],0))
 for source in SOURCES:
  dst=frozen/'DiophantineConsistency'/source.name;shutil.copyfile(source,dst)
  if H(dst)!=PINS[source]:raise ValueError(('client freeze drift',source.name))
  imports=[v for line in dst.read_text().splitlines() if line.startswith('import ') for v in line[7:].split()]
  rows.append(('DiophantineConsistency.'+source.stem,dst,PINS[source],imports,1))
 runs=[]
 for label in ('author','peer'):
  run=out/label;run.mkdir();lib=run/'lib';monitor.overlay(PREFIX/label/'lib',lib)
  env=os.environ.copy()
  for key in tuple(env):
   if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
  env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);steps=[]
  for name,src,digest,imports,report_count in rows:
   rel=Path(*name.split('.'));obj=(lib/rel).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=run/(name.replace('.','_')+'.log')
   if obj.exists() or obj.is_symlink():raise ValueError(('output path occupied',label,name))
   cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={frozen}',str(src),'-o',str(obj)]
   code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text();reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
   if code or reason or not policy.accepted(name,src,text) or 'error:' in text or 'sorryAx' in text or len(reports)!=report_count:raise ValueError(('compiler failure',label,name,code,reason,text[-8000:]))
   expected_reports={'DiophantineConsistency.FreeJSaturationClient':{'FreeJSaturationClient.graph_saturation'}}.get(name,set())
   if {report for report,_ in reports}!=expected_reports or any({x.strip() for x in ax.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for _,ax in reports):raise ValueError(('unexpected axiom report',name,reports))
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
 receipt={'status':'PASS_PAIRED_FREEJ_SATURATION_CLIENT','runs':runs,'population_audit':review,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Conditional free-J model saturation with explicit beta, radix, repunit, port split and mask-population assumptions. No compact44 port binding, checker, machine simulation, or PRA proof. No full package/dynamic ancestry audit.'}
 with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_PAIRED_FREEJ_SATURATION_CLIENT',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
