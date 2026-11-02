#!/usr/bin/env python3
"""Source-frozen paired nine-module free-J population client rebuild."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent; BASE=HERE.parent; ROOT=HERE.parents[2]
PLAN=BASE/'free-j-population-closure-plan'; AUDIT=ROOT/'reviews/ordinary12-freej-power-finish-independent-audit'
PLAN_AUDIT=ROOT/'reviews/ordinary12-freej-population-closure-independent-audit/CHECK.json'
PREFIX=Path('/tmp/ipra-freej-power-finish-pair-01'); PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'; LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SOURCES=(HERE/'FreeJPopulationFactsNarrow.lean',HERE/'FreeJPopulationClient.lean')
PINS={MONITOR: '2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 PLAN/'scan.json': '4233970a7eb5b20b40d1c9f3565d4e713c3354363d1d3e1d99929df7fb8d598a',
 PLAN/'scan.py': '56f8de2291ce201e4ea88f98f352b2cbb2e967040773f948f4df0d58a7e28706',
 PLAN/'README.md': 'f56ceafbe759b380ba60a34a1e8071a2a2a2273c906f3f21a8f4575eec1471af',
 AUDIT/'audit.py': 'e7030ec0f1fd00202fa6b90fc76be9ca968b987af7cd21aeca1fd666c80ea378',
 AUDIT/'CHECK.json': '1f0357d7cb23f09fe6079e5ee744f7cf8cab6bd06d96b6e80b3167fbc9c86d7b',
 AUDIT/'terminal-observation.json': '4c31bc2dfc6ad4c4e111c655b46401ce0ceeb9e25a2a988632be71b945ab6160',
 PLAN_AUDIT: '6c8c1db91c70c2d380a1886fa60686447e92838fb44259536c0c31ed6d98e619',
 SOURCES[0]: '95d95753a6c6cd8e2f4c4e64061f0add162fe6ea73bb1463d4df20ad30ac1baa',
 SOURCES[1]: '093599333a80a90234c83d225705952ef02e4b6f525d9aed63c22b60b7837ef8'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(path):
 spec=importlib.util.spec_from_file_location('monitor',path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def warnings_accepted(name,src,text):
 if name=='DiophantineConsistency.ArithmeticBinomLegendre':
  expected=(f"{src}:78:10: warning: try 'simp' instead of 'simpa'\n\n"
    "Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`\n")
  return text==expected
 return 'warning:' not in text

def verify():
 for p,h in PINS.items():
  if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
 scan=json.loads((PLAN/'scan.json').read_text());review=json.loads((AUDIT/'CHECK.json').read_text());obs=json.loads((AUDIT/'terminal-observation.json').read_text());plan_review=json.loads(PLAN_AUDIT.read_text())
 if scan['status']!='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD' or len(scan['preferred_rebuild'])!=9 or len(scan['freej_base_objects'])!=97:raise ValueError('invalid scan')
 if review.get('status')!='PASS_INDEPENDENT_FREEJ_POWER_FINISH_AUDIT' or review.get('recorded_outer_exit')!=0 or obs.get('audit_observed_exit_code')!=0:raise ValueError('invalid power audit')
 if plan_review.get('status')!='PASS_INDEPENDENT_FREEJ_POPULATION_CLOSURE_SOURCE_AUDIT' or plan_review.get('wording_correction_commit')!='9c04a203e2' or plan_review.get('normal_scan_exit')!=0 or plan_review.get('preferred_modules')!=9 or plan_review.get('freej_objects_per_side')!=97:raise ValueError('invalid closure audit')
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,text=True,timeout=120)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=scan:raise ValueError(('source closure drift',proc.returncode,proc.stderr))
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,text=True,timeout=900)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=review:raise ValueError(('power audit rerun failed',proc.returncode,proc.stderr))
 return scan,review

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
 if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-freej-population-client-pair-') or out.exists() or out.is_symlink():raise ValueError('use a fresh direct /tmp/ipra-freej-population-client-pair-* path')
 scan,review=verify(); monitor=load(MONITOR);out.mkdir(); frozen=out/'frozen';frozen.mkdir();rows=[]
 for row in scan['preferred_rebuild']:
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
  seed=lib/'DiophantineConsistency/FreeJPowerFinish.olean'
  if seed.exists() or seed.is_symlink():raise ValueError('power seed path occupied')
  shutil.copyfile(PREFIX/label/'FreeJPowerFinish.olean',seed)
  if H(seed)!=scan['freej_power_seed'][label]['sha256']:raise ValueError(('power seed drift',label))
  env=os.environ.copy()
  for key in tuple(env):
   if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
  env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);steps=[]
  for name,src,digest,imports,report_count in rows:
   rel=Path(*name.split('.'));obj=(lib/rel).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=run/(name.replace('.','_')+'.log')
   if obj.exists() or obj.is_symlink():raise ValueError(('output path occupied',label,name))
   cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={frozen}',str(src),'-o',str(obj)]
   code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text();reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
   if code or reason or not warnings_accepted(name,src,text) or 'error:' in text or 'sorryAx' in text or len(reports)!=report_count:raise ValueError(('compiler failure',label,name,code,reason,text[-8000:]))
   expected_reports={'DiophantineConsistency.FreeJPopulationFactsNarrow':{'FreeJPopulationFacts.population_of_ordinary_facts'},'DiophantineConsistency.FreeJPopulationClient':{'FreeJPopulationClient.graph_population'}}.get(name,set())
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
  runs.append({'label':label,'power_seed_sha256':H(seed),'steps':steps})
 if [{k:v for k,v in r.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')} for r in runs[0]['steps']]!=[{k:v for k,v in r.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')} for r in runs[1]['steps']]:raise ValueError('paired outputs differ')
 scan2,review2=verify()
 if scan2!=scan or review2!=review:raise ValueError('parent inputs changed')
 receipt={'status':'PASS_PAIRED_FREEJ_POPULATION_CLIENT','runs':runs,'power_audit':review,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Conditional free-J model population bound; beta>=46 and radix equality retained. No compact44 port binding, checker, machine simulation, or PRA proof. No full package/dynamic ancestry audit.'}
 with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_PAIRED_FREEJ_POPULATION_CLIENT',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
