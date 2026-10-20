#!/usr/bin/env python3
"""Offline deterministic reconstruction and proof-certificate replay for K222.

Python3.10+ and its standard library suffice. Default freshly checks source,
all-natural emitter, schematic finite logic, literal decoder, two all-tape
folds and exact blank startup, then audits retained runtime evidence.
--full freshly derives all6167 primary unbounded runtime cases.
--baseline additionally replays inherited K224 quick certificates.
--full-baseline additionally rederives inherited K224/K225/K226 runtimes.
The included alternative is reconstructed by default; --full-alternative
also freshly rederives its runtime. No mode downloads files or builds Rocq/Lean.
"""
from pathlib import Path,PurePosixPath
import argparse,csv,hashlib,json,os,shutil,stat,subprocess,sys,time,zipfile
ROOT=Path(__file__).resolve().parent
PACKET=ROOT.parent
BASE='K224_Construction_2026-10-20'
BASE_SHA='cf5db8d08a34f5661ad1266226809ed1f0099fd38374c66d127e1e06519c6887'

def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def dump(p,d):Path(p).write_text(json.dumps(d,indent=2)+'\n')
def same(a,b):
 need(Path(a).read_bytes()==Path(b).read_bytes(),'Reproduced bytes differ: '+str(a));return sha(a)
def relative(n):
 need(type(n) is str and n and '\\' not in n and ':' not in n and '\x00' not in n,'Unsafe path')
 p=PurePosixPath(n);need(not p.is_absolute() and all(x not in ('','.','..') for x in n.rstrip('/').split('/')),'Unsafe path')
 return Path(*p.parts)
def manifest():
 d=read(ROOT/'manifest.json');need(d.get('schema_version')==1,'Manifest schema');seen=set()
 for x in d['files']:
  p=ROOT/relative(x['path']);need(x['path'] not in seen and p.is_file() and not p.is_symlink(),'Missing/duplicate/nonregular file');seen.add(x['path'])
  need(p.stat().st_size==x['size'] and sha(p)==x['sha256'],'Manifest mismatch: '+x['path'])
 actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file() and p!=ROOT/'manifest.json'}
 need(actual==seen,'Portable inventory differs from manifest')
 return dict(status='PORTABLE_MANIFEST_PASS',files=len(seen),sha256=sha(ROOT/'manifest.json'))
def extract_baseline(dest):
 archive=ROOT/'vendor'/f'{BASE}.zip';need(sha(archive)==BASE_SHA,'Baseline archive pin');dest.mkdir()
 with zipfile.ZipFile(archive) as z:
  seen=set()
  for e in z.infolist():
   rel=relative(e.filename);need(rel.parts[0]==BASE and rel not in seen,'Unexpected/duplicate ZIP member');seen.add(rel)
   kind=stat.S_IFMT((e.external_attr>>16)&0xffff);need(kind in (0,stat.S_IFREG,stat.S_IFDIR) and not e.flag_bits&1,'Unsupported ZIP member')
   target=dest/rel
   if e.is_dir():target.mkdir(parents=True,exist_ok=True)
   else:
    target.parent.mkdir(parents=True,exist_ok=True)
    with z.open(e) as src,target.open('xb') as dst:shutil.copyfileobj(src,dst)
    need(target.stat().st_size==e.file_size,'ZIP extraction size')
 return dest/BASE

def stored_runtime_audit(machine):
 r=read(ROOT/'certificates/runtime222.json');cases=read(ROOT/'certificates/runtime222_cases.json');sites=read(machine/'sites.json')
 need(r['status']=='UNIVERSAL_MATHEMATICAL_PASS','Stored runtime status')
 need(r['table_sha256']==sha(machine/'candidate222.legacy.tm') and r['sites_sha256']==sha(machine/'sites.json'),'Runtime inputs differ')
 for key,name in [('checker_sha256','check_literal_runtime.py'),('engine_sha256','symbolic_runtime.py'),('helper_sha256','independent_runtime.py')]:need(r[key]==sha(ROOT/'runtime'/name),'Runtime checker bytes differ')
 keys=[(i,b) for i,x in enumerate(sites) for b in ((False,True) if x[1]=='CD' else (False,))]
 need([(x['site_index'],x['positive']) for x in cases]==keys and len(keys)==6167,'Guarded-case coverage')
 need(len(cases)==r['cases'] and sum(x['symbolic_steps'] for x in cases)==r['symbolic_steps']==1488390,'Runtime accounting')
 need(min(x['duration'][0] for x in cases)==r['minimum_actual_steps']==13,'Positive duration bound')
 for x in cases:need(len(x['duration'])==13 and min(x['duration'])>=0 and x['duration'][0]>0,'Nonpositive duration coefficient')
 rows=[]
 for line in (machine/'candidate222.legacy.tm').read_text().splitlines():
  if line and not line.startswith('#'):rows.append(list(map(int,line.split()[:2])))
 need(sorted(rows)==r['directly_used_rows'] and len(rows)==444 and r['working_states']==222,'Literal row coverage')
 return dict(status='STORED_RUNTIME_INTEGRITY_AND_COVERAGE_PASS',cases=6167,symbolic_rules=1488390,rows=444,minimum_actual_steps=13,fresh_derivation=False,scope='Integrity and complete-case audit of supplied prior unbounded derivations. Use --full to derive them anew.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output-dir',type=Path,required=True)
 ap.add_argument('--full',action='store_true');ap.add_argument('--baseline',action='store_true');ap.add_argument('--full-baseline',action='store_true');ap.add_argument('--full-alternative',action='store_true');ap.add_argument('--skip-alternative',action='store_true')
 a=ap.parse_args();need(sys.version_info>=(3,10),'Python3.10+ required');need(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),'Keep assertions enabled')
 out=a.output_dir.resolve();need(out!=PACKET and PACKET not in out.parents,'Output must be outside the packet');need(not out.exists() or out.is_dir() and not any(out.iterdir()),'Use an initially empty output directory')
 out.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir();(out/'logic').mkdir();start=time.monotonic()
 result=dict(schema_version=1,status='IN_PROGRESS',phases=[],fresh_primary_runtime=a.full,fresh_inherited_baseline_runtime=a.full_baseline,fresh_Rocq_or_Lean_build=False)
 env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}
 def save():result['seconds']=time.monotonic()-start;dump(out/'replay.json',result)
 def run(name,script,*args):
  print('[K222] '+name,flush=True);log=out/'logs'/(name+'.log');begin=time.monotonic()
  with log.open('w') as stream:p=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],cwd=out,env=env,stdout=stream,stderr=subprocess.STDOUT)
  result['phases'].append(dict(name=name,returncode=p.returncode,seconds=time.monotonic()-begin,log=log.relative_to(out).as_posix()));save()
  need(p.returncode==0,'Phase failed: '+name+'; see '+str(log))
 try:
  result['manifest']=manifest()
  # Primary input lineage is available intact. No fresh baseline replay is
  # implied when the user has not selected either baseline flag.
  need(sha(ROOT/'vendor'/f'{BASE}.zip')==BASE_SHA,'Wrong inherited ZIP')
  result['baseline']=dict(archive_sha256=BASE_SHA,replayed=False,fresh_runtime=False)
  if a.baseline or a.full_baseline:
   base=extract_baseline(out/'baseline-input');flags=['--full','--full-baseline'] if a.full_baseline else []
   run('01_inherited_baseline',base/'portable/reproduce.py','--output-dir',out/'baseline-replay',*flags)
   br=read(out/'baseline-replay/replay.json');need(br['status'] in ('QUICK_REPLAY_PASS','FULL_REPLAY_PASS'),'Inherited baseline failed')
   result['baseline']=dict(archive_sha256=BASE_SHA,replayed=True,fresh_runtime=a.full_baseline,status=br['status'])
  run('02_source_and_all_natural_emitter',ROOT/'source/check_seed_g_source.py','--source',ROOT/'machine/sites.json','--output',out/'source_receipt.json','--write-source',out/'sites.json')
  same(out/'sites.json',ROOT/'machine/sites.json')
  sr=read(out/'source_receipt.json');need(sr['status']=='SEED_G222_EXACT_ALL_NATURAL_EMITTER_AND_SOURCE_PASS','Source status')
  run('03_fresh_uniform_logic',ROOT/'source/logic/check_seed_g_logic.py','--output',out/'logic/logic_receipt.json','--proofs',out/'logic/proofs.json')
  same(out/'logic/proofs.json',ROOT/'source/logic/seed_g_logic_proofs.json')
  run('04_independent_logic_parser',ROOT/'verification/independent_seed_logic.py',out/'logic/proofs.json','--output',out/'logic/independent_receipt.json')
  run('05_decoder_table_and_blank_start',ROOT/'verification/build_seed222.py','--parent-table',ROOT/'inputs/parent224.k.tm','--parent-sites',ROOT/'source/inputs/parent225_sites.json','--sites',out/'sites.json','--legacy-map',ROOT/'inputs/legacy_state_map.json','--output-dir',out/'machine')
  machine=out/'machine'
  hashes={}
  for n in ('candidate222.tm','candidate222.k.tm','candidate222.legacy.tm','parent_seed_g224.k.tm','sites.json','state_map.json','bootstrap.json'):hashes[n]=same(machine/n,ROOT/'machine'/n)
  run('05b_independent_dense_startup',ROOT/'verification/check_dense_startup.py','--table',machine/'candidate222.tm','--sparse-bootstrap',machine/'bootstrap.json','--output',out/'dense_bootstrap.json')
  same(out/'dense_bootstrap.json',ROOT/'machine/dense_bootstrap.json')
  run('06_all_tape_folds',ROOT/'verification/check_seed_folds.py','--parent',machine/'parent_seed_g224.k.tm','--candidate',machine/'candidate222.k.tm','--specification',ROOT/'certificates/folds.json','--output',out/'fold_certificate.json')
  run('06b_independent_fold_implementation',ROOT/'verification/independent_fold_audit.py','--parent',machine/'parent_seed_g224.k.tm','--candidate',machine/'candidate222.k.tm','--folds',ROOT/'certificates/fold_list.json','--output',out/'independent_folds.json')
  run('06c_negative_controls',ROOT/'verification/check_negative_controls.py','--parent',machine/'parent_seed_g224.k.tm','--specification',ROOT/'certificates/folds.json','--output',out/'negative_controls.json')
  same(out/'negative_controls.json',ROOT/'certificates/negative_controls.json')
  result['stored_runtime']=stored_runtime_audit(machine)
  if a.full:
   run('07_fresh_unbounded_runtime',ROOT/'runtime/check_literal_runtime.py','--table',machine/'candidate222.legacy.tm','--sites',machine/'sites.json','--states','222','--output',out/'runtime222.json')
   same(out/'runtime222_cases.json',ROOT/'certificates/runtime222_cases.json')
   rr=read(out/'runtime222.json');need(rr['status']=='UNIVERSAL_MATHEMATICAL_PASS' and rr['cases']==6167 and len(rr['directly_used_rows'])==444,'Fresh runtime result differs')
   result['fresh_runtime']=dict(status=rr['status'],cases=rr['cases'],symbolic_rules=rr['symbolic_steps'],rows=len(rr['directly_used_rows']))
  if not a.skip_alternative and (ROOT/'alternative/reproduce.py').exists():
   flags=['--full'] if a.full_alternative else []
   run('08_conditional_alternative',ROOT/'alternative/reproduce.py','--output-dir',out/'alternative',*flags)
   result['alternative']=dict(replayed=True,fresh_runtime=a.full_alternative)
  else:result['alternative']=dict(replayed=False,fresh_runtime=False)
  result['final_manifest']=manifest()
  result.update(status='FULL_K222_REPLAY_PASS' if a.full else 'QUICK_K222_REPLAY_PASS',working_states=222,transition_rows=444,source_instructions=4744,source_dag_nodes=208,guarded_cases=6167,canonical_table_sha256=hashes['candidate222.tm'],source_sha256=hashes['sites.json'],uniform_logic_proof_sha256=sha(out/'logic/proofs.json'),artifact_hashes=hashes,proof_status='Exact construction and ordinary mathematical finite/unbounded certificates, with retained inherited ZFC calibration. No new Rocq/Lean endpoint; no proof of absolute consistency.')
  save();print(json.dumps(result,indent=2));return 0
 except Exception as e:
  result.update(status='FAILED',error=repr(e));save();print('FAILED: '+repr(e),file=sys.stderr);return 1
if __name__=='__main__':raise SystemExit(main())
