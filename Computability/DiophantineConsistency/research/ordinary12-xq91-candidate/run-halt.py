#!/usr/bin/env python3
"""Guarded selected union and bounded 91-graph all-model halt check."""
from pathlib import Path
from hashlib import sha256
import json,os,shutil,subprocess,sys,tempfile,time
if sys.flags.optimize:raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent;D=H.parents[1]
a=os.environ.get('ATTEMPT','attempt01')
if not a.startswith('attempt') or not a[7:].isdigit():raise SystemExit('invalid attempt')
OBS=H/'observations'/('halt-'+a)
if OBS.exists():raise SystemExit('refusing to overwrite observation')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
BASE=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
BASELIB=Path('/tmp/qcube92-halt-5apqi7f7/lib')
AUDIT=D/'reviews/ordinary12-xq91-serialized-import-independent/observations/attempt01/result.json'
AUDIT_PIN='87f7fad28524346b6921bda2f180f763417e98a0209063a7fae7fb579aea3787'
BASE_PIN='8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'
EXTRA=[('XQ91','algebra-attempt01','647ab4935265c9db60a9f6b4975f3eb48bc14426b2d102fc10c969730232db6a'),('XQ91Model','model-attempt01','bdc4d6cb11c87d0161b0d777f2be050ef6bbf7ca11d6a5ce1b88a345d21ce36b')]

def need(v,m):
 if not v:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'non-file '+str(p))
 return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
def resource():
 lines=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();ps=[]
 for line in lines:
  f=line.strip().split(None,3)
  if len(f)>=2 and f[1]=='lean':
   rss=int(f[2]) if len(f)>2 and f[2].isdigit() else None
   ps.append({'pid':int(f[0]),'rss_kib':rss,'args':f[3] if len(f)>3 else ' '.join(f[2:])})
 m=next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
 return {'time_ns':time.time_ns(),'mem_available_kib':int(m.split()[1]),'lean':ps}
def basecheck(base):
 actual={p.relative_to(BASELIB).as_posix():rec(p) for p in BASELIB.rglob('*') if p.is_file()}
 need(actual==base['union'] and len(actual)==1291,'base union drift')
 return actual
def extras(base):
 out={}
 for name,attempt,pin in EXTRA:
  receipt=H/'observations'/attempt/'terminal.json';need(sha(receipt)==pin,'receipt drift '+name);d=json.loads(receipt.read_text());src=H/(name+'.lean');obj=Path(d['output_root'])/(name+'.olean')
  need(d['exit']==0 and not d['reason'] and d['selected_provider_unchanged'] and d['before']==d['after'],'producer failure '+name)
  need(obj.is_file() and sha(obj)==d['object_sha256'] and sha(src)==d['before'][str(src)],'producer drift '+name)
  for suf in ('.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash'):
   need(not os.path.lexists(str(obj)[:-len('.olean')]+suf),'unexpected producer companion '+name+suf)
  out[name]={'receipt':str(receipt),'receipt_sha256':sha(receipt),'object':str(obj),'object_sha256':sha(obj),'source_sha256':sha(src)}
 priorobj=Path(base['output_root'])/'QCube92Halt.olean';priorsrc=D/'research/ordinary12-qcube92-candidate/QCube92Halt.lean'
 need(base['exit']==0 and not base['reason'] and base['base_unchanged'] and base['extra_unchanged'] and base['union_unchanged'],'prior halt failure')
 need(priorobj.is_file() and sha(priorobj)==base['object_sha256'] and sha(priorsrc)==base['source_sha256']==base['source_after'],'prior halt drift')
 out['QCube92Halt']={'receipt':str(BASE),'receipt_sha256':sha(BASE),'object':str(priorobj),'object_sha256':sha(priorobj),'source_sha256':sha(priorsrc)}
 for suf in ('.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash'):
  need(not os.path.lexists(str(priorobj)[:-len('.olean')]+suf),'unexpected prior halt companion '+suf)
 return out

def auditcheck(base,addition):
 need(sha(AUDIT)==AUDIT_PIN,'serialized ancestry audit pin mismatch')
 d=json.loads(AUDIT.read_text());need(d['exit']==0,'serialized header scan failed')
 need(d['planned_imports']==['XQ91Model','QCube92Halt','DiophantineConsistency.FreeJRadixAlignment'],'planned imports drift')
 need(len(d['planned_project_ancestors'])==741,'planned ancestry size drift')
 need('DiophantineConsistency.FreeJGraphCongruenceExplore' in d['planned_project_ancestors'],'symbolic alignment is outside recorded closure')
 need(base['union']['DiophantineConsistency/FreeJGraphCongruenceExplore.olean']['sha256']=='545daf0eff0f2cc4576b456fd6f73e84a714fe3759d8cdff71874497fd20b448','symbolic alignment object drift')
 for forbidden in ('FreeJRootBinding','QCube92Existence','FreeJRadixAlignment'):
  need(forbidden not in d['planned_project_ancestors'],'forbidden duplicate module '+forbidden)
 for path,expected in d['pins'].items():need(Path(path).is_file() and sha(path)==expected,'serialized audit input drift '+path)
 checked={}
 for root,row in d['roots'].items():
  rel=root.replace('.','/')+'.olean'
  expected=base['union'][rel]['sha256'] if rel in base['union'] else addition[root]['object_sha256']
  need(d['objects'][root]['sha256']==expected,'root hash mismatch '+root)
  for mod,v in row['selected'].items():
   rel=mod.replace('.','/')+'.olean'
   expected=base['union'][rel]['sha256'] if rel in base['union'] else addition[mod]['object_sha256']
   need(v['sha256']==expected,'selected ancestry mismatch '+mod)
   path=v['path']
   if path not in checked:
    obj=Path(path);need(obj.is_file() and str(obj.resolve())==v['realpath'] and sha(obj)==expected,'selected ancestry drift '+mod)
    checked[path]=expected
 for mod in d['planned_project_ancestors']:
  rel=mod.replace('.','/')+'.olean'
  need(rel in base['union'] or mod in addition,'missing planned ancestor '+mod)
 return True

need(LEAN.is_file() and PACKAGE.is_dir(),'missing tool or package')
need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk guard')
need(sha(BASE)==BASE_PIN,'base receipt mismatch');base=json.loads(BASE.read_text()); before=basecheck(base);addition=extras(base)
auditcheck(base,addition)
initial=resource();need(initial['mem_available_kib']>=8*1024**2 and len(initial['lean'])<2,'resource guard')
OBS.mkdir(parents=True);out=Path(tempfile.mkdtemp(prefix='xq91-halt-'));lib=out/'lib';lib.mkdir()
for name,value in before.items():
 dest=lib/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(value['resolved'])
for name,value in addition.items():
 dest=lib/(name+'.olean');need(not dest.exists(),'extra shadows existing '+name);dest.symlink_to(Path(value['object']).resolve(strict=True))
union={p.relative_to(lib).as_posix():rec(p) for p in lib.rglob('*') if p.is_file()}
need(len(union)==1294,'wrong union count')
imports={}
for source in [H/'XQ91.lean',H/'XQ91Model.lean',H/'XQ91Halt.lean']:
 names=[]
 for line in source.read_text().splitlines():
  if line.startswith('import '):
   for name in line.removeprefix('import ').split():
    path=name.replace('.','/')+'.olean';need(path in union,'missing declared import '+path);names.append({'module':name,'sha256':union[path]['sha256']})
 imports[source.name]=names
need([x['module'] for x in imports['XQ91Halt.lean']]==['XQ91Model','QCube92Halt','DiophantineConsistency.FreeJRadixAlignment'],'client imports differ from audited plan')
src=H/'XQ91Halt.lean';copy=out/src.name;shutil.copyfile(src,copy);shutil.copyfile(src,OBS/'source.txt');sourcehash=sha(src);runnerhash=sha(H/'run-halt.py');leanhash=sha(LEAN)
env={'PATH':'/usr/bin:/bin','LEAN_PATH':f'{lib}:{PACKAGE}','LEAN_NUM_THREADS':'1'}
cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={out}',str(copy),'-o',str(out/'XQ91Halt.olean')]
samples=[];start=time.monotonic();reason=None
with (out/'stdout').open('x') as so,(out/'stderr').open('x') as se:
 proc=subprocess.Popen(cmd,env=env,stdout=so,stderr=se,text=True)
 try:
  while proc.poll() is None:
   snap=resource();samples.append(snap)
   if snap['mem_available_kib']<8*1024**2 or len(snap['lean'])>2:reason='resource guard';break
   if time.monotonic()-start>180:reason='timeout';break
   time.sleep(2)
 except Exception as exc:
  reason='monitor error: '+repr(exc)
 finally:
  if reason and proc.poll() is None:proc.kill()
  proc.wait()
stdout=(out/'stdout').read_text();stderr=(out/'stderr').read_text();(OBS/'stdout').write_text(stdout);(OBS/'stderr').write_text(stderr)
afterbase=basecheck(base);afteraddition=extras(base)
auditcheck(base,afteraddition)
after={p.relative_to(lib).as_posix():rec(p) for p in lib.rglob('*') if p.is_file()};obj=out/'XQ91Halt.olean'
result={'command':cmd,'lean_path':env['LEAN_PATH'],'output_root':str(out),'exit':proc.returncode,'reason':reason,'elapsed':time.monotonic()-start,'source_sha256':sourcehash,'source_after':sha(src),'runner_sha256':runnerhash,'runner_after':sha(H/'run-halt.py'),'lean_sha256':leanhash,'lean_after':sha(LEAN),'serialized_audit_sha256':sha(AUDIT),'base_receipt_sha256':sha(BASE),'base_count':len(before),'base_unchanged':before==afterbase,'extra':addition,'extra_unchanged':addition==afteraddition,'union_count':len(union),'union':union,'union_unchanged':union==after,'declared_imports':imports,'preflight':initial,'samples':samples,'object_sha256':sha(obj) if obj.is_file() else None,'stdout_sha256':sha(OBS/'stdout'),'stderr_sha256':sha(OBS/'stderr'),'scope':'Selected-project author union; inherited source-object, package-transitive and dynamic ancestry; no iPRA derivation.'}
(OBS/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:result[k] for k in ('exit','reason','elapsed','output_root','object_sha256','base_count','union_count','base_unchanged','extra_unchanged','union_unchanged')}));print(stdout);print(stderr,file=sys.stderr)
need(proc.returncode==0 and not reason and obj.is_file() and before==afterbase and addition==afteraddition and union==after and sha(src)==sourcehash and sha(LEAN)==leanhash and sha(H/'run-halt.py')==runnerhash and sha(BASE)==BASE_PIN and not any(t in stdout+stderr for t in ('error:','warning:','sorryAx')),'halt compile failed')
