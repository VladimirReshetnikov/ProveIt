#!/usr/bin/env python3
"""Bounded, author-only exploratory build; not a paired replay or audit."""
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,sys,traceback
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
SEED=Path('/tmp/ipra-graph-marked-explore-03/lib')
SEED_PROGRESS=SEED.parent/'progress.json'
SEED_PREFLIGHT=SEED.parent/'preflight.json'
ORIGINAL=SEED.parent/'frozen/DiophantineConsistency/ArithmeticWangTable.lean'
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
MON=ROOT/'research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py'
PINS={
 'manifest':'5c48ab43ebfbaada2798ee24e08fb277e350f8b1c434c5c78a404d84187103a4',
 'progress':'db82f9d3152a21711416986e7aee63c4f0383dd0d81b82c74fa8df56aa80cbc3',
 'preflight':'1bb2439027ec20561c481417582bf0b700ab80124975d0ccac9e1004d41b542b',
 'original':'8bf620443a3ed74892efba1aeaa6f8c14add5feaff4954dda001a6acf5e36ff2',
 'monitor':'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 'lean':'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
SUF=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def need(x,msg):
 if not x:raise ValueError(msg)
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rec(p):
 if not os.path.lexists(p):return None
 need(p.is_file(),('nonregular or dangling',str(p)))
 return {'realpath':str(p.resolve(strict=True)),'sha256':H(p)}
def slots(stem):return {str(Path(str(stem)+s)):rec(Path(str(stem)+s)) for s in SUF}
def check(records):
 for p,v in records.items():need(rec(Path(p))==v,('slot changed',p))
def main():
 need(__debug__ and not sys.flags.optimize,'optimized Python rejected')
 need(not any(k.startswith('LD_') or k in ('LEAN_SRC_PATH','LEAN_SYSROOT') for k in os.environ),'unsafe loader environment')
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--preflight-only',action='store_true');args=ap.parse_args()
 out=args.output;need(out.is_absolute() and out.parent.is_dir() and out.parent.resolve().is_relative_to(Path('/tmp')),'output must be under /tmp')
 need(not os.path.lexists(out),'output path already exists');need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk below 4 GiB')
 for path,key in [(HERE/'source-manifest.json','manifest'),(SEED_PROGRESS,'progress'),(SEED_PREFLIGHT,'preflight'),(ORIGINAL,'original'),(MON,'monitor'),(LEAN,'lean')]:
  need(path.is_file() and H(path)==PINS[key],('pinned input changed',str(path)))
 progress=json.loads(SEED_PROGRESS.read_text())['steps'];need(len(progress)==82 and all(x['compiler_exit']==0 for x in progress[:81]) and progress[81]['compiler_exit']==1,'unexpected seed history')
 manifest=json.loads((HERE/'source-manifest.json').read_text());rows=manifest['sources'];need(len(rows)==96,'source count')
 names=[x['module'] for x in rows];need(len(names)==len(set(names)) and names[-1]=='DiophantineConsistency.ArithmeticWangTable','source order')
 for row in rows:
  src=HERE/row['source'];need(src.is_file() and not src.is_symlink() and H(src)==row['sha256'],('source changed',str(src)))
  row['imports']=re.findall(r'^import\s+([\w.]+)',src.read_text(),re.M);need(row['imports'],('no imports',row['module']))
 spec=importlib.util.spec_from_file_location('resource_monitor',MON);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
 out.mkdir();lib=out/'lib';frozen=out/'frozen';frozen.mkdir();monitor.overlay(SEED,lib)
 env={'PATH':'/usr/bin:/bin','HOME':'/home/codex','LEAN_PATH':str(lib)+':'+str(PKG)}
 sourceguards={};directguards={};built=set();inputs={}
 for row in rows:
  name=row['module'];src=HERE/row['source'];dest=(frozen/Path(*name.split('.'))).with_suffix('.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
  need(H(dest)==row['sha256'] and not dest.is_symlink(),('frozen mismatch',name));sourceguards[str(dest)]=row['sha256']
  stem=lib/Path(*name.split('.'));need(all(x is None for x in slots(stem).values()),('output slot collision',name))
  found={}
  for dep in ['Init']+row['imports']:
   if dep in built:found[dep]='earlier source';continue
   need(dep not in names,('out-of-order import',name,dep));rel=Path(*dep.split('.')).with_suffix('.olean');choices=[x for x in (lib/rel,PKG/rel) if x.is_file()]
   need(choices,('missing input',name,dep));chosen=choices[0]
   need(all(H(x)==H(chosen) for x in choices),('conflicting direct input',name,dep))
   found[dep]=rec(chosen);directguards.update(slots(Path(str(chosen)[:-6])))
  inputs[name]=found;built.add(name)
 check(directguards)
 pre={'status':'READY_AUTHOR_ONLY_NO_LEAN','source_count':len(rows),'seed':str(SEED),'seed_history':'81 successful children; child 82 failed; inherited provider ancestry not authenticated','source_pins':sourceguards,'direct_inputs':inputs,'direct_companion_slots':directguards,'limitations':'sampled resource limits; package/transitive ancestry inherited; dependency queries are timeout-bounded without RSS monitoring'}
 (out/'preflight.json').write_text(json.dumps(pre,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':pre['status'],'sources':len(rows),'direct_slots':len(directguards)}),flush=True)
 if args.preflight_only:return
 steps=[]
 for pos,row in enumerate(rows,1):
  check(directguards)
  for path,sha in sourceguards.items():
   p=Path(path);need(p.is_file() and not p.is_symlink() and H(p)==sha,('frozen source drift',path))
  name=row['module'];src=(frozen/Path(*name.split('.'))).with_suffix('.lean');stem=lib/Path(*name.split('.'));obj=Path(str(stem)+'.olean')
  need(all(v is None for v in slots(stem).values()),('late output collision',name))
  expected=set()
  for dep in ['Init']+row['imports']:
   rel=Path(*dep.split('.')).with_suffix('.olean');chosen=next((p for p in (lib/rel,PKG/rel) if p.is_file()),None);need(chosen is not None,('missing current input',name,dep));expected.add(str(chosen.resolve()))
  dp=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120)
  got={str(Path(x).resolve()) for x in dp.stdout.splitlines() if x.strip()};need(dp.returncode==0 and not dp.stderr and got==expected,('dependency mismatch',name,dp.returncode,dp.stdout,dp.stderr,sorted(expected)))
  log=out/(str(pos).zfill(3)+'-'+name.replace('.','_')+'.log');cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={frozen}',str(src),'-o',str(obj)]
  code,peak,reason=monitor.monitored(cmd,env,log,timeout=120);step={'position':pos,'module':name,'compiler_exit':code,'peak_sampled_rss_bytes':peak,'reason':reason,'log':str(log),'log_sha256':H(log),'deps_stdout':dp.stdout,'disk_free_bytes':shutil.disk_usage('/tmp').free};steps.append(step)
  (out/'progress.json').write_text(json.dumps({'steps':steps},indent=2)+'\n');print(json.dumps(step),flush=True)
  need(type(code) is int and code==0 and reason is None,('child failed',name,code,reason))
  text=log.read_text();need(not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text),('diagnostic rejected',name))
  need(obj.is_file() and not obj.is_symlink(),('missing or linked output',name));snapshot=slots(stem);need(all((v is not None) if p==str(obj) else v is None for p,v in snapshot.items()),('unexpected output companion',name));directguards.update(snapshot);check(directguards)
 check(directguards)
 for path,sha in sourceguards.items():need(Path(path).is_file() and not Path(path).is_symlink() and H(Path(path))==sha,('final source drift',path))
 (out/'RESULT.json').write_text(json.dumps({'status':'PASS_AUTHOR_ONLY_CHUNKED_TABLE','steps':steps,'limitations':pre['limitations']},indent=2)+'\n');print('PASS_AUTHOR_ONLY_CHUNKED_TABLE',flush=True)
try:main()
except Exception as exc:
 print('EXPLORATION_FAILED',repr(exc),flush=True);traceback.print_exc();sys.exit(1)
