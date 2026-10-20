#!/usr/bin/env python3
"""Offline reconstruction and mathematical-certificate replay for both K222s.

The default checks reconstruction, exact emitters, finite logical certificates,
both initializers, and retained runtime integrity/coverage. --full rederives all
final unbounded runtime cases. Neither mode is a new Rocq/Lean kernel build.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,os,shutil,subprocess,sys,time

ROOT=Path(__file__).resolve().parent
def need(ok,message):
 if not ok:raise ValueError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def dump(path,data):path.write_text(json.dumps(data,indent=2)+'\n')
def same(a,b):need(a.read_bytes()==b.read_bytes(),'Reproduced bytes differ: '+str(a));return sha(a)
def manifest():
 path=ROOT/'MANIFEST.json'
 if not path.exists():raise ValueError('Missing package manifest')
 data=json.loads(path.read_text());seen=set()
 for item in data['files']:
  name=item['path'];p=PurePosixPath(name)
  need(not p.is_absolute()and all(x not in('','..','.')for x in p.parts),'Unsafe manifest path')
  need(name not in seen,'Duplicate manifest member');seen.add(name)
  f=ROOT/Path(*p.parts)
  need(f.is_file()and not f.is_symlink(),'Missing or nonregular manifest member: '+name)
  need(f.stat().st_size==item['size']and sha(f)==item['sha256'],'Manifest digest differs: '+name)
 return dict(status='MANIFEST_PASS',files=len(seen),sha256=sha(path))
def runtime_audit(variant,source,legacy,receipt,casepath):
 data=json.loads(receipt.read_text());cases=json.loads(casepath.read_text());sites=json.loads(source.read_text())
 need(data['status']=='UNIVERSAL_MATHEMATICAL_PASS','Stored runtime is incomplete')
 need(data['table_sha256']==sha(legacy)and data['sites_sha256']==sha(source),'Runtime input binding')
 expected=[(i,p)for i,s in enumerate(sites)for p in((False,True)if s[1]=='CD'else(False,))]
 need([(c['site_index'],c['positive'])for c in cases]==expected,'Runtime case coverage')
 need(data['cases']==len(expected)==({'conditional':5956,'seed':6167}[variant]),'Runtime census')
 need(all(len(c['duration'])==13 and c['duration'][0]>0 and
  all(type(n)is int and n>=0 for n in c['duration'])for c in cases),'Invalid affine duration')
 rows={(int(line.split()[0]),int(line.split()[1]))for line in legacy.read_text().splitlines()
  if line and not line.startswith('#')}
 need(set(map(tuple,data['directly_used_rows']))==rows and len(rows)==444,'Runtime row coverage')
 need(sum(c['symbolic_steps']for c in cases)==data['symbolic_steps'],'Runtime step census')
 for key,name in [('engine_sha256','symbolic_runtime.py'),('helper_sha256','independent_runtime.py')]:
  need(data[key]==sha(ROOT/'code/runtime'/name),'Runtime engine pin differs')
 if 'cases_sha256'in data:need(data['cases_sha256']==sha(casepath),'Runtime cases hash binding')
 return dict(status='RUNTIME_INTEGRITY_AND_COVERAGE_PASS',variant=variant,cases=len(cases),
  rows=len(rows),cases_sha256=sha(casepath),symbolic_steps=data['symbolic_steps'])
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--output-dir',type=Path,required=True)
 ap.add_argument('--full',action='store_true')
 a=ap.parse_args();need(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
 out=a.output_dir.resolve();need(out!=ROOT and ROOT not in out.parents,'Use an output directory outside the packet')
 need(not out.exists()or(out.is_dir()and not any(out.iterdir())),'Use an initially empty output directory')
 out.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir()
 started=time.monotonic();receipt=dict(status='IN_PROGRESS',mode='full'if a.full else'quick',phases=[])
 def run(name,script,*args):
  log=out/'logs'/(name+'.log');t=time.monotonic();print(name,flush=True)
  with log.open('w')as f:
   p=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],cwd=out,stdout=f,stderr=subprocess.STDOUT,
    env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
  receipt['phases'].append(dict(name=name,returncode=p.returncode,seconds=time.monotonic()-t,log=log.relative_to(out).as_posix()))
  dump(out/'replay.json',receipt);need(p.returncode==0,'Failed phase '+name+'; see '+str(log))
 try:
  receipt['manifest']=manifest()
  C=ROOT/'vendor/conditional223';S=ROOT/'vendor/seed223';support=ROOT/'code/support'
  cal=C/'calibration'
  run('01_parent_conditional_calculus',cal/'verify_conditional_source.py',
   '--base-sites',cal/'baseline224_sites.json','--candidate-sites',C/'sites.json',
   '--certificate',cal/'conditional_fusion_certificate.json','--output',out/'parent_conditional_calculus.json')
  run('02_construct_conditional',ROOT/'code/construct222.py','--baseline-source',C/'sites.json',
   '--baseline-table',C/'candidate.k.tm','--output-dir',out/'conditional-source')
  run('03_conditional_emitter',ROOT/'code/check_emitter222.py','--baseline-source',C/'sites.json',
   '--baseline-table',C/'candidate.k.tm','--candidate-source',out/'conditional-source/sites.json',
   '--output',out/'conditional-source/emitter.json')
  for name in('candidate222.tm','candidate222.k.tm','sites.json','parent224.k.tm'):
   same(out/'conditional-source'/name,ROOT/'machines/conditional'/name)
  run('04_construct_seed',ROOT/'code/construct_seed222.py','--support-dir',support,
   '--baseline-source',S/'sites.json','--baseline-table',S/'candidate.k.tm',
   '--baseline-grammar',S/'grammar223.json','--output-dir',out/'seed-source')
  run('05_seed_emitter',ROOT/'code/check_seed_emitter222.py','--support-dir',support,
   '--baseline-source',S/'sites.json','--baseline-table',S/'candidate.k.tm',
   '--candidate-source',out/'seed-source/sites.json','--output',out/'seed-source/emitter.json')
  for name in('candidate222.tm','candidate.k.tm','sites.json'):
   same(out/'seed-source'/name,ROOT/'machines/seed'/name)
  logic=out/'logic';logic.mkdir()
  for name in('combined_helper_certificate.py','merged_euclidean_helper_certificate.py','review_logic.py'):
   shutil.copyfile(ROOT/'code/logic'/name,logic/name)
  run('06_G_finite_proof',logic/'merged_euclidean_helper_certificate.py')
  same(logic/'merged_euclidean_helper_proofs.json',ROOT/'evidence/logic/merged_euclidean_helper_proofs.json')
  run('07_G_independent_review',logic/'review_logic.py',logic/'merged_euclidean_helper_proofs.json',
   '--output',logic/'independent_review.json')
  receipt['candidates']={}
  for variant,ktname in(('conditional','candidate222.k.tm'),('seed','candidate.k.tm')):
   fresh=out/(variant+'-source');machine=out/(variant+'-machine');retained=ROOT/'machines'/variant
   run(variant+'_08_machine_and_sparse_startup',ROOT/'code/check_machine.py','--table',fresh/ktname,
    '--variant',variant,'--legacy-map',ROOT/'vendor/legacy_state_map.json','--output-dir',machine)
   for name in('candidate222.tm','candidate.legacy.tm'):same(machine/name,retained/name)
   run(variant+'_09_dense_startup',ROOT/'code/runtime/check_blank_dense.py','--table',fresh/ktname,
    '--output',machine/'bootstrap_dense.json')
   sparse=json.loads((machine/'machine_check.json').read_text())
   dense=json.loads((machine/'bootstrap_dense.json').read_text())
   need(sparse['one_cells']==dense['one_cells']and sparse['head']==dense['head'],'Independent startup mismatch')
   if a.full:
    run(variant+'_10_unbounded_runtime',ROOT/'code/runtime/check_literal_runtime.py',
     '--table',machine/'candidate.legacy.tm','--sites',fresh/'sites.json','--states',222,
     '--output',machine/'runtime.json')
    retained_cases=ROOT/'evidence'/variant/'runtime_cases.json'
    need(json.loads((machine/'runtime_cases.json').read_text())==json.loads(retained_cases.read_text()),
     'Fresh case derivations differ from retained ones')
    rpath,cpath=machine/'runtime.json',machine/'runtime_cases.json'
   else:rpath,cpath=ROOT/'evidence'/variant/'runtime.json',ROOT/'evidence'/variant/'runtime_cases.json'
   audit=runtime_audit(variant,fresh/'sites.json',machine/'candidate.legacy.tm',rpath,cpath)
   audit.update(canonical_sha256=sha(machine/'candidate222.tm'),bootstrap_steps=409835,
    fresh_unbounded_derivations=a.full)
   receipt['candidates'][variant]=audit;dump(out/'replay.json',receipt)
  receipt.update(status='FULL_K222_REPLAY_PASS'if a.full else'QUICK_K222_REPLAY_PASS',
   seconds=time.monotonic()-started,
   proof_status='Ordinary mathematical certificates and inherited ZFC calibrations; no new Rocq or Lean endpoint.')
  dump(out/'replay.json',receipt)
  print(json.dumps({k:v for k,v in receipt.items()if k!='phases'},indent=2))
 except Exception as e:
  receipt.update(status='FAILED',error=repr(e),seconds=time.monotonic()-started)
  dump(out/'replay.json',receipt);raise
if __name__=='__main__':main()
