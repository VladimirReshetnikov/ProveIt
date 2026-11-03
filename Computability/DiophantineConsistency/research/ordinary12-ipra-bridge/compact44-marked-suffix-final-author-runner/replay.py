#!/usr/bin/env python3
"""Bounded, author-only marked suffix; not a paired replay or audit."""
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,sys,traceback
from pathlib import Path
HERE=Path(__file__).resolve().parent
DC=HERE.parents[2];REPO=DC.parents[1]
PLAN=HERE.parent/'compact44-marked-suffix-final-source-plan'
PRIOR=HERE.parent/'compact44-graph-marked-join-plan'
AUDIT=DC/'reviews/compact44-marked-suffix-final-source-independent-review'
PARENT=DC/'reviews/compact44-wang-chunk-author-artifact-independent-audit'
HIST=DC/'reviews/ha87-isolated-full-author-pass'
WARNING_RULES={
 'DiophantineConsistency.ArithmeticWangPlane':('cfe5c8bdc328291ded007cbb8181797d55292608ccc4eef264100103839fbcf9','fb85934b5529859319550f2c14fa002f0983bb163cdc24aec8d2b3e754a5ef27',2,'6db38ab5d8c4ccdae9406fd92269e618cd31f4803246ad33f46d88204c0b9ac8'),
 'DiophantineConsistency.ArithmeticWangStrip':('87297fe92e3f6d1df0266c1f19a8f45d69cfc0e8e9a167e292bfca9628336b2f','c9b9d15e042fd9f35e62f13937bcc36ee169ca869aefb1d300b82651bbadb29a',1,'7b8d1d8e81daf210b0390264e9cb622ad8262e4b81b8f33a0005793b4116074c'),
 'DiophantineConsistency.ArithmeticWangSoundness':('583535a73f2e4700aabd94291148ca7f254c5c0b85c335237137c512d57b2643','3e5486008d4701a9db2c635f16c1d4d7694c70f5657529fd5b6b8b4e98389f6e',1,'93ad55b2c786f26df91a1a5b25c6392e537bbb738e2ec19897db8263221522e7')}
SEED=Path('/tmp/ipra-wang-chunk-author-build-02/lib')
SEED_RESULT=SEED.parent/'RESULT.json'
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
MON=DC/'research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py'
PINS={
 'history_state':'84c3bc6f6c34c47e67278c43df8580444d32e2946844a4c40c31cfd747f33a90',
 'plan_scan':'e90d141ec1083001b8d7504d9cc961ea5473fac79ea36f6cc090281651cd006b',
 'plan_script':'97ce365edfd74f1614badf1c4bb6cd2b84ac594d8a88d20f683e0b9da6b5193c',
 'prior_source':'2aeb7400ef18c7cd4bc0c74b1ca09b53e0c685f6054e99d92617f3af9bab7cc6',
 'prior_busy':'abe89bf1cf589a8146771707d322c663012e03e63a7e4e605df486b808f19846',
 'closure_check':'b55a08a7efa315baa2973bbed07b1d1c5e9276663cd55e42f4f1cbbe0ba51134',
 'closure_terminal':'5bf2cb4e37d640a9def266e83c12bf06e98242ecca3e0cf0f58539efd192eb94',
 'closure_audit':'6d67b8f03e9648ee42bebc63381aa789f90ce0c3957c53ca6a0efb5ee32d0cd7',
 'parent_check':'59dd1eefe5fc2d46bbb0ca7b2d83e14bcc1de9b692da98e94c5598f17678945e',
 'parent_terminal':'af62d28207cca0c6d6163b4f46731919031600bd69d5efddc1a41dbe509e6b9a',
 'parent_audit':'a48b7684dc27fff4705419d30fbf14a62fb99f9ac302edcd79b1d508bccbcda1',
 'seed_result':'f79b98bb500a0cf2af5dfda7f7341468348bfc4f53664d6e15fb804902a23a3d',
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
def warning_baseline():
 state=HIST/'state.json'
 need(state.is_file() and H(state)==PINS['history_state'],'historical warning state changed')
 data=json.loads(state.read_text());result={}
 for name,(source_sha,log_sha,count,norm_sha) in WARNING_RULES.items():
  log=HIST/'logs'/(name.replace('.','_')+'-attempt-1.log')
  need(log.is_file() and H(log)==log_sha,('historical warning log changed',name))
  records=[x for x in data['records'] if x.get('module')==name and x.get('source_sha256')==source_sha and x.get('exit')==0 and x.get('verified') is True]
  need(len(records)==1,'historical warning record count')
  r=records[0];need(r.get('log_sha256')==log_sha and r.get('log_file')==log.name,'historical warning record mismatch')
  paths=[x for x in r['command'] if x.endswith('/'+name.split('.')[-1]+'.lean')];need(len(paths)==1,'historical source path mismatch')
  text=log.read_text();normalized=text.replace(paths[0],'<SOURCE>')
  need(text.count(paths[0])==count and text.count('warning:')==count and hashlib.sha256(normalized.encode()).hexdigest()==norm_sha,('historical warning content mismatch',name))
  result[name]=normalized
 return result
def accepted_diagnostics(name,src,sha,text,baselines):
 need(not re.search(r'(?m)^.*error:|\bsorryAx\b|\bsorry\b',text),('diagnostic rejected',name))
 if 'warning:' not in text:return text
 rule=WARNING_RULES.get(name);need(rule is not None,('diagnostic rejected',name))
 source_sha,_,count,_=rule
 need(sha==source_sha and text.count(str(src))==count and text.count('warning:')==count and text.replace(str(src),'<SOURCE>')==baselines[name],('diagnostic rejected',name))
 need(warning_baseline()==baselines,'historical warning baseline drift')
 return ''
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
def run_closure_audit(out,label,expected):
 cmd=[sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')]
 clean={'PATH':'/usr/bin:/bin','HOME':'/home/codex'}
 r=subprocess.run(cmd,cwd=REPO,env=clean,text=True,capture_output=True,timeout=900)
 (out/(label+'.stdout')).write_text(r.stdout);(out/(label+'.stderr')).write_text(r.stderr)
 meta={'command':cmd,'exit_code':r.returncode,'stdout_sha256':H(out/(label+'.stdout')),'stderr_sha256':H(out/(label+'.stderr'))}
 (out/(label+'.json')).write_text(json.dumps(meta,indent=2)+'\n')
 need(r.returncode==0 and not r.stderr,('closure audit failed',label,r.returncode,r.stderr[-1000:]))
 need(json.loads(r.stdout)==expected,('closure audit result differs',label))
 return meta

def main():
 need(__debug__ and not sys.flags.optimize,'optimized Python rejected')
 baseline=warning_baseline()
 need(not any(k.startswith('LD_') or k in ('LEAN_SRC_PATH','LEAN_SYSROOT') for k in os.environ),'unsafe loader environment')
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--preflight-only',action='store_true');args=ap.parse_args()
 out=args.output;need(out.is_absolute() and out.parent.is_dir() and out.parent.resolve().is_relative_to(Path('/tmp')),'output must be under /tmp')
 need(not os.path.lexists(out),'output path already exists');need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk below 4 GiB')
 pins=[(PLAN/'source-scan.json','plan_scan'),(PLAN/'scan.py','plan_script'),
       (PRIOR/'source-scan.json','prior_source'),(PRIOR/'busybeaver-source-scan.json','prior_busy'),
       (AUDIT/'CHECK.json','closure_check'),(AUDIT/'terminal-observation.json','closure_terminal'),(AUDIT/'audit.py','closure_audit'),
       (PARENT/'CHECK.json','parent_check'),(PARENT/'terminal-observation.json','parent_terminal'),(PARENT/'audit.py','parent_audit'),
       (SEED_RESULT,'seed_result'),(MON,'monitor'),(LEAN,'lean')]
 for path,key in pins:need(path.is_file() and H(path)==PINS[key],('pinned input changed',str(path)))
 closure=json.loads((AUDIT/'CHECK.json').read_text()); parent=json.loads((PARENT/'CHECK.json').read_text())
 need(closure.get('status')=='PASS_NO_LEAN_FINAL_MARKED_SUFFIX_SOURCE_REVIEW' and closure.get('reviewed_commit')=='e4f98fbd0f' and closure.get('scan_sha256')==PINS['plan_scan'] and closure.get('source_count')==22 and closure.get('changed_position')==22 and closure.get('direct_modules')==26 and closure.get('candidate_slots')==520 and closure.get('target_slots')==440 and closure.get('prior_inventories_equal') is True and closure.get('lean_launched') is False and all(type(closure.get(k)) is int and closure[k]==v for k,v in {'author_scan_rerun_exit':0,'optimized_scan_exit':1}.items()),'closure schema mismatch')
 need(closure.get('isolated_source_sha256')=='342f43800e6892e78bcb8c781a2d1ee6a396a40b1d5b2da01c90e7edc727c5a7' and closure.get('isolated_log_sha256')=='3ac5bf9a677c0692978bb2d174014a1b5d2c5ad35d5b3d45e4a5369f33e1c707' and closure.get('isolated_reports')==16 and closure.get('failed_wrapper_logs_checked')==22,'isolated observation mismatch')
 need(closure.get('parent_check_sha256')=='9def6a93cd07d214c6957522e1f54c772a988936667e625fe2413f51c3c9535c' and type(closure.get('parent_review_exit')) is int and closure['parent_review_exit']==0,'parent review mismatch')
 need(parent.get('status')=='PASS_INDEPENDENT_AUTHOR_ONLY_WANG_ARTIFACT_AUDIT' and parent.get('result_sha256')==PINS['seed_result'],'parent schema mismatch')
 seed=json.loads(SEED_RESULT.read_text());need(seed.get('status')=='PASS_AUTHOR_ONLY_CHUNKED_TABLE' and len(seed.get('steps',[]))==96,'seed result schema mismatch')
 manifest=json.loads((PLAN/'source-scan.json').read_text());rows=manifest['sources'];need(manifest.get('status')=='PASS_SOURCE_ONLY_SUFFIX_SCAN' and len(rows)==22,'source scan schema mismatch')
 names=[x['module'] for x in rows];need(len(names)==len(set(names)) and names[-1]=='DiophantineConsistency.MarkedSuffixInventory','source order')
 prior=json.loads((PRIOR/'busybeaver-source-scan.json').read_text())['ordered_sources']+json.loads((PRIOR/'source-scan.json').read_text())['ordered_sources'];need(len(prior)==100,'prior source count')
 for old,row in zip(prior[82:],rows[:18]):
  name=old['module'] if '.' in old['module'] else 'DiophantineConsistency.'+old['module'];need(row['module']==name and Path(row['source'])==REPO/old['source'] and row['sha256']==old['sha256'],('prior source identity mismatch',name))
 for row in rows:
  src=Path(row['source']);need(src.is_file() and not src.is_symlink() and src.resolve().is_relative_to(REPO) and H(src)==row['sha256'],('source changed',str(src)))
  imports=re.findall(r'^import\s+([\w.]+)',src.read_text(),re.M);need(imports==row['imports'] and imports,('import mismatch',row['module']))
 need(sum(len(re.findall(r'^#print\s+axioms\s+([\w.]+)\s*$',Path(r['source']).read_text(),re.M)) for r in rows)==58,'unexpected report inventory size')
 spec=importlib.util.spec_from_file_location('resource_monitor',MON);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
 no_link_dirs(SEED)
 out.mkdir();before_audit=run_closure_audit(out,'closure-audit-before',closure)
 lib=out/'lib';frozen=out/'frozen';frozen.mkdir();monitor.overlay(SEED,lib)
 safe_dir(out,lib);safe_dir(out,frozen);no_link_dirs(lib)
 env={'PATH':'/usr/bin:/bin','HOME':'/home/codex','LEAN_PATH':str(lib)+':'+str(PKG)}
 sourceguards={};directguards={};built=set();inputs={}
 for row in rows:
  name=row['module'];src=Path(row['source']);dest=(frozen/Path(*name.split('.'))).with_suffix('.lean');ensure_dir(out,dest.parent);need(not os.path.lexists(dest),('frozen source collision',str(dest)));shutil.copyfile(src,dest);safe_dir(out,dest.parent)
  need(H(dest)==row['sha256'] and not dest.is_symlink(),('frozen mismatch',name));sourceguards[str(dest)]=row['sha256']
  stem=lib/Path(*name.split('.'));pkgstem=PKG/Path(*name.split('.'));safe_dir(out,stem.parent)
  need(all(x is None for x in slots(stem).values()) and all(x is None for x in slots(pkgstem).values()),('output slot collision',name))
  merge_guards(directguards,slots(pkgstem))
  found={}
  for dep in ['Init']+row['imports']:
   rel=Path(*dep.split('.')).with_suffix('.olean');libpath=lib/rel;pkgpath=PKG/rel
   merge_guards(directguards,slots(Path(str(pkgpath)[:-6])))
   if dep in built:
    found[dep]={'kind':'produced','path':str(libpath)}
    continue
   need(dep not in names,('out-of-order import',name,dep))
   merge_guards(directguards,slots(Path(str(libpath)[:-6])))
   reviewed=manifest['direct_candidates'].get(dep);need(reviewed is not None,('unreviewed direct dependency',name,dep))
   candidates={c['root']:c for c in reviewed['candidates']};need(set(candidates)=={str(SEED),str(PKG)},('candidate roots differ',dep))
   for suf in SUF:
    original=str((SEED/Path(*dep.split('.'))))+suf; fresh=str((lib/Path(*dep.split('.'))))+suf
    package=str((PKG/Path(*dep.split('.'))))+suf
    need(rec(Path(fresh))==candidates[str(SEED)]['slots'][original] and rec(Path(package))==candidates[str(PKG)]['slots'][package],('candidate differs from reviewed scan',dep,suf))
   choices=[x for x in (libpath,pkgpath) if x.is_file()]
   need(choices,('missing input',name,dep));chosen=choices[0]
   need(all(H(x)==H(chosen) for x in choices),('conflicting direct input',name,dep))
   found[dep]={'kind':'static','path':str(chosen),'record':rec(chosen)}
  inputs[name]=found;built.add(name)
 check(directguards)
 pre={'status':'READY_AUTHOR_ONLY_SUFFIX_NO_LEAN','source_count':len(rows),'seed':str(SEED),'seed_history':'independently artifact-audited 96-child author-only split table; its exploratory prefix and transitive provider ancestry remain unauthenticated','source_pins':sourceguards,'closure_audit_before':before_audit,'direct_inputs':inputs,'direct_companion_slots':directguards,'limitations':'sampled resource limits; package/transitive ancestry inherited; dependency queries are timeout-bounded without RSS monitoring'}
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
  code,peak,reason=monitor.monitored(cmd,env,log,timeout=600);step={'position':pos,'module':name,'compiler_exit':code,'peak_sampled_rss_bytes':peak,'reason':reason,'log':str(log),'log_sha256':H(log),'deps_command':[str(LEAN),'--deps',str(src)],'deps_stdout':dp.stdout,'compiler_command':cmd,'disk_free_bytes':shutil.disk_usage('/tmp').free};steps.append(step)
  (out/'progress.json').write_text(json.dumps({'steps':steps},indent=2)+'\n');print(json.dumps(step),flush=True)
  need(type(code) is int and code==0 and reason is None,('child failed',name,code,reason))
  text=log.read_text();clean_text=accepted_diagnostics(name,src,row['sha256'],text,baseline)
  reports=report_inventory(src.read_text(),clean_text)
  need(obj.is_file() and not obj.is_symlink(),('missing or linked output',name));snapshot=slots(stem);need(all((v is not None) if p==str(obj) else v is None for p,v in snapshot.items()),('unexpected output companion',name));merge_guards(directguards,snapshot);outputs[name]=rec(obj);step['output_slots']=snapshot;step['axiom_reports']=reports
  (out/'progress.json').write_text(json.dumps({'steps':steps},indent=2)+'\n');check(directguards);safe_dir(out,stem.parent);safe_dir(out,src.parent)
 check(directguards);no_link_dirs(lib);no_link_dirs(frozen);need(warning_baseline()==baseline,'historical warning baseline drift')
 after_audit=run_closure_audit(out,'closure-audit-after',closure)
 check(directguards);no_link_dirs(lib);no_link_dirs(frozen);need(warning_baseline()==baseline,'historical warning baseline drift')
 for path,sha in sourceguards.items():need(Path(path).is_file() and not Path(path).is_symlink() and H(Path(path))==sha,('final source drift',path))
 (out/'RESULT.json').write_text(json.dumps({'status':'PASS_AUTHOR_ONLY_MARKED_SUFFIX','steps':steps,'closure_audit_before':before_audit,'closure_audit_after':after_audit,'final_direct_and_output_slots':directguards,'limitations':pre['limitations']},indent=2)+'\n');print('PASS_AUTHOR_ONLY_MARKED_SUFFIX',flush=True)
if __name__=='__main__':
 try:main()
 except Exception as exc:
  print('EXPLORATION_FAILED',repr(exc),flush=True);traceback.print_exc();sys.exit(1)
