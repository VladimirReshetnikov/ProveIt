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
def merge_guards(records,new):
 for path,value in new.items():
  need(path not in records or records[path]==value,('inconsistent repeated observation',path))
  records[path]=value
def check(records):
 for p,v in records.items():need(rec(Path(p))==v,('slot changed',p))
def safe_dir(root,path):
 root=Path(root);path=Path(path)
 need(root.is_dir() and not root.is_symlink(),('unsafe root directory',str(root)))
 try: parts=path.relative_to(root).parts
 except ValueError: raise ValueError(('directory outside output',str(path)))
 cur=root
 for part in parts:
  cur=cur/part;need(cur.is_dir() and not cur.is_symlink(),('unsafe directory',str(cur)))
 need(path.resolve().is_relative_to(root.resolve()),('directory escaped output',str(path)))
def ensure_dir(root,path):
 root=Path(root);path=Path(path);safe_dir(root,root)
 try: parts=path.relative_to(root).parts
 except ValueError: raise ValueError(('directory outside output',str(path)))
 cur=root
 for part in parts:
  safe_dir(root,cur);cur=cur/part
  if not os.path.lexists(cur):cur.mkdir()
  safe_dir(root,cur)
def no_link_dirs(root):
 for parent,dirs,_ in os.walk(root,followlinks=False):
  for name in dirs:need(not (Path(parent)/name).is_symlink(),('linked overlay directory',str(Path(parent)/name)))
def report_inventory(source,output):
 names=re.findall(r'^#print\s+axioms\s+([\w.]+)\s*$',source,re.M)
 need(len(names)==len(set(names)),'duplicate requested report')
 pat=re.compile(r"(?m)^'([^']+)' (?:(?:depends on axioms:\s*\[([^\]]*)\])|(does not depend on any axioms))")
 matches=list(pat.finditer(output));got={}
 for m in matches:
  name=m.group(1);need(name not in got,('duplicate axiom report',name))
  vals=[] if m.group(3) else [x.strip() for x in m.group(2).split(',') if x.strip()]
  need((m.group(3) or vals) and len(vals)==len(set(vals)) and set(vals)<={'propext','Classical.choice','Quot.sound'},('unpermitted or empty axiom report',name,vals))
  got[name]=vals
 need(set(got)==set(names),('axiom report names differ',sorted(names),sorted(got)))
 need(not pat.sub('',output).strip(),('unexpected compiler output',pat.sub('',output)[:1000]))
 return got
def resolve_mapping(mapping,outputs,lib,pkg):
 expected=set()
 for dep,item in mapping.items():
  chosen=Path(item['path']);current=rec(chosen)
  target=outputs.get(dep) if item['kind']=='produced' else item['record']
  need(target is not None and current==target,('input differs from preflight mapping',dep,str(chosen)))
  rel=Path(*dep.split('.')).with_suffix('.olean')
  first=next((x for x in (lib/rel,pkg/rel) if x.is_file()),None)
  need(first==chosen,('input resolution changed',dep,str(first),str(chosen)))
  expected.add(current['realpath'])
 return expected
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
 need(sum(len(re.findall(r'^#print\s+axioms\s+([\w.]+)\s*$',(HERE/r['source']).read_text(),re.M)) for r in rows)==94,'unexpected report inventory size')
 spec=importlib.util.spec_from_file_location('resource_monitor',MON);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
 no_link_dirs(SEED)
 out.mkdir();lib=out/'lib';frozen=out/'frozen';frozen.mkdir();monitor.overlay(SEED,lib)
 safe_dir(out,lib);safe_dir(out,frozen);no_link_dirs(lib)
 env={'PATH':'/usr/bin:/bin','HOME':'/home/codex','LEAN_PATH':str(lib)+':'+str(PKG)}
 sourceguards={};directguards={};built=set();inputs={}
 for row in rows:
  name=row['module'];src=HERE/row['source'];dest=(frozen/Path(*name.split('.'))).with_suffix('.lean');ensure_dir(out,dest.parent);need(not os.path.lexists(dest),('frozen source collision',str(dest)));shutil.copyfile(src,dest);safe_dir(out,dest.parent)
  need(H(dest)==row['sha256'] and not dest.is_symlink(),('frozen mismatch',name));sourceguards[str(dest)]=row['sha256']
  stem=lib/Path(*name.split('.'));safe_dir(out,stem.parent);need(all(x is None for x in slots(stem).values()),('output slot collision',name))
  found={}
  for dep in ['Init']+row['imports']:
   rel=Path(*dep.split('.')).with_suffix('.olean');libpath=lib/rel;pkgpath=PKG/rel
   merge_guards(directguards,slots(Path(str(pkgpath)[:-6])))
   if dep in built:
    found[dep]={'kind':'produced','path':str(libpath)}
    continue
   need(dep not in names,('out-of-order import',name,dep))
   merge_guards(directguards,slots(Path(str(libpath)[:-6])))
   choices=[x for x in (libpath,pkgpath) if x.is_file()]
   need(choices,('missing input',name,dep));chosen=choices[0]
   need(all(H(x)==H(chosen) for x in choices),('conflicting direct input',name,dep))
   found[dep]={'kind':'static','path':str(chosen),'record':rec(chosen)}
  inputs[name]=found;built.add(name)
 check(directguards)
 pre={'status':'READY_AUTHOR_ONLY_NO_LEAN','source_count':len(rows),'seed':str(SEED),'seed_history':'81 successful children; child 82 failed; inherited provider ancestry not authenticated','source_pins':sourceguards,'direct_inputs':inputs,'direct_companion_slots':directguards,'limitations':'sampled resource limits; package/transitive ancestry inherited; dependency queries are timeout-bounded without RSS monitoring'}
 (out/'preflight.json').write_text(json.dumps(pre,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':pre['status'],'sources':len(rows),'direct_slots':len(directguards)}),flush=True)
 if args.preflight_only:return
 steps=[];outputs={}
 for pos,row in enumerate(rows,1):
  check(directguards);safe_dir(out,lib);safe_dir(out,frozen);no_link_dirs(lib);no_link_dirs(frozen)
  for path,sha in sourceguards.items():
   p=Path(path);need(p.is_file() and not p.is_symlink() and H(p)==sha,('frozen source drift',path))
  name=row['module'];src=(frozen/Path(*name.split('.'))).with_suffix('.lean');stem=lib/Path(*name.split('.'));obj=Path(str(stem)+'.olean')
  safe_dir(out,stem.parent);safe_dir(out,src.parent)
  need(all(v is None for v in slots(stem).values()),('late output collision',name))
  expected=resolve_mapping(inputs[name],outputs,lib,PKG)
  dp=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120)
  got={str(Path(x).resolve()) for x in dp.stdout.splitlines() if x.strip()};need(dp.returncode==0 and not dp.stderr and got==expected,('dependency mismatch',name,dp.returncode,dp.stdout,dp.stderr,sorted(expected)))
  check(directguards);safe_dir(out,stem.parent);safe_dir(out,src.parent)
  need(resolve_mapping(inputs[name],outputs,lib,PKG)==expected,('resolution changed after dependency query',name))
  need(src.is_file() and not src.is_symlink() and H(src)==row['sha256'],('source changed after dependency query',name))
  need(all(v is None for v in slots(stem).values()),('output changed after dependency query',name))
  log=out/(str(pos).zfill(3)+'-'+name.replace('.','_')+'.log');cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={frozen}',str(src),'-o',str(obj)]
  code,peak,reason=monitor.monitored(cmd,env,log,timeout=120);step={'position':pos,'module':name,'compiler_exit':code,'peak_sampled_rss_bytes':peak,'reason':reason,'log':str(log),'log_sha256':H(log),'deps_command':[str(LEAN),'--deps',str(src)],'deps_stdout':dp.stdout,'compiler_command':cmd,'disk_free_bytes':shutil.disk_usage('/tmp').free};steps.append(step)
  (out/'progress.json').write_text(json.dumps({'steps':steps},indent=2)+'\n');print(json.dumps(step),flush=True)
  need(type(code) is int and code==0 and reason is None,('child failed',name,code,reason))
  text=log.read_text();need(not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text),('diagnostic rejected',name))
  reports=report_inventory(src.read_text(),text)
  need(obj.is_file() and not obj.is_symlink(),('missing or linked output',name));snapshot=slots(stem);need(all((v is not None) if p==str(obj) else v is None for p,v in snapshot.items()),('unexpected output companion',name));merge_guards(directguards,snapshot);outputs[name]=rec(obj);step['output_slots']=snapshot;step['axiom_reports']=reports
  (out/'progress.json').write_text(json.dumps({'steps':steps},indent=2)+'\n');check(directguards);safe_dir(out,stem.parent);safe_dir(out,src.parent)
 check(directguards);no_link_dirs(lib);no_link_dirs(frozen)
 for path,sha in sourceguards.items():need(Path(path).is_file() and not Path(path).is_symlink() and H(Path(path))==sha,('final source drift',path))
 (out/'RESULT.json').write_text(json.dumps({'status':'PASS_AUTHOR_ONLY_CHUNKED_TABLE','steps':steps,'final_direct_and_output_slots':directguards,'limitations':pre['limitations']},indent=2)+'\n');print('PASS_AUTHOR_ONLY_CHUNKED_TABLE',flush=True)
if __name__=='__main__':
 try:main()
 except Exception as exc:
  print('EXPLORATION_FAILED',repr(exc),flush=True);traceback.print_exc();sys.exit(1)
