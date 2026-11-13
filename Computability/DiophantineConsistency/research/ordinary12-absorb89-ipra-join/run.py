#!/usr/bin/env python3
"""Guarded 89 iPRA endpoint atop the independently audited 90 author join."""
from pathlib import Path
from hashlib import sha256
import importlib.util,json,os,re,shutil,sys,tempfile,traceback
H=Path(__file__).resolve().parent;D=H.parents[1]
R=D/'research/ordinary12-direct90-ipra-join/run-v9.py'
P=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
S=H/'observations/scan-attempt02/result.json'
SOURCE=D/'research/ordinary12-absorb89-ipra-endpoint-draft/Absorb89IPRAEndpoint.lean'
OBS=H/'observations/join-attempt01'
if OBS.exists():raise SystemExit('refusing to overwrite')
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
RUNNER_PIN='117ca7e29a4822832ffbe8a213431c89c770f1f51ddaa9ee11efee4b7fe15f03'
JOIN_PIN='09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed'
SCAN_PIN='7f2a1a85f7406e72e717efaa160fdbce4207fbd7c3fd7098dc266448fd38fbd0'
SOURCE_PIN='dad83ae6a217eaffeec8b1a6d6813ad1c69a3f280a0ac2056f2d71aa95e567f4'
for p,h in [(R,RUNNER_PIN),(P,JOIN_PIN),(S,SCAN_PIN),(SOURCE,SOURCE_PIN)]:need(sha(p)==h,'input pin '+str(p))
spec=importlib.util.spec_from_file_location('reviewedv9',R);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
for p in [m.LEAN,m.HELPER,m.INVENTORY]:need(sha(p)==m.PINS[p],'tool pin '+str(p))
old=json.loads(P.read_text());scan=json.loads(S.read_text());need(old['status']=='PASS' and scan['status']=='PASS','predecessor status')
oldroot=Path(old['output_root'])/'lib'; c=scan['closure']; report=scan['report']
need(report['selected']==787 and report['outside']==44 and len(report['matched'])==765 and len(report['missing'])==22 and not report['mismatched'],'unexpected closure comparison')
need(set(c['project'])==set(report['matched'])|set(report['missing']),'missing classifications')
need(not ({'FreeJRootBinding','FreeJSignedTransport'}&set(c['project'])),'namespace collision')
def guard_records():
 for name,row in c['project'].items():
  stem=str(row['path'])[:-len('.olean')]
  need(m.rec(row['path'])==row['record'] and {s:m.rec(stem+s) for s in m.SUFFIXES}==row['companions'],'selected producer drift '+name)
  target=oldroot/m.relative_module(name)
  need({s:m.rec(str(target)+s) for s in m.SUFFIXES}==row['join_provider'],'old union drift '+name)
 for name,row in old['post_headers']['project'].items():
  stem=str(row['path'])[:-len('.olean')]
  need(m.rec(row['path'])==row['record'] and {s:m.rec(stem+s) for s in m.SUFFIXES}==row['companions'],'old endpoint provider drift '+name)
 m.recheck_outside(c);m.recheck_outside(old['post_headers'])
 for p,h in [(R,RUNNER_PIN),(P,JOIN_PIN),(S,SCAN_PIN),(SOURCE,SOURCE_PIN)]:need(sha(p)==h,'input drift '+str(p))
 for p in [m.LEAN,m.HELPER,m.INVENTORY]:need(sha(p)==m.PINS[p],'tool drift '+str(p))
OBS.mkdir(parents=True);temp=Path(tempfile.mkdtemp(prefix='absorb89-ipra-join-'));out=temp/'lib';src=temp/'src';out.mkdir();src.mkdir()
result={'status':'FAILED','output_root':str(temp),'runner_sha256':sha(__file__),'scan_sha256':sha(S),'prior_join_sha256':sha(P),'scope':'selected project serialized closure and guarded author join; no independent Lean replay; package-transitive, dynamic, and complete source-object ancestry inherited'}
try:
 guard_records()
 old_snapshot={p.relative_to(oldroot).as_posix():m.rec(p) for p in oldroot.rglob('*') if p.is_file()}
 for rel,record in old_snapshot.items():
  target=out/rel;target.parent.mkdir(parents=True,exist_ok=True);need(not os.path.lexists(target),'union collision '+rel);os.symlink(record['resolved'],target)
 for n in report['missing']:
  row=c['project'][n];stem=out/m.relative_module(n);stem.parent.mkdir(parents=True,exist_ok=True)
  for suffix,record in row['companions'].items():
   if record is not None:
    target=Path(str(stem)+suffix);need(not os.path.lexists(target),'supplement collision '+n+suffix);os.symlink(record['resolved'],target)
 def snapshot():return {p.relative_to(out).as_posix():m.rec(p) for p in out.rglob('*') if p.is_file()}
 initial=snapshot();result['union_initial_count']=len(initial);result['union_initial_sha256']=sha256(json.dumps(initial,sort_keys=True).encode()).hexdigest()
 guard_records();copy=src/SOURCE.name;shutil.copyfile(SOURCE,copy);shutil.copyfile(SOURCE,OBS/'source.lean');need(sha(copy)==sha(OBS/'source.lean')==SOURCE_PIN,'copied source')
 env={'PATH':'/usr/bin:/bin','LEAN_PATH':f'{out}:{m.PACKAGE}','LEAN_NUM_THREADS':'1'}
 obj=out/'Absorb89IPRAEndpoint.olean';need(not obj.exists(),'endpoint collision')
 cmd=[str(m.LEAN),'-M3000','-j1','-DElab.async=false',f'--root={src}',str(copy),'-o',str(obj)]
 stdout,stderr=m.monitored(cmd,env,OBS,'endpoint',180)
 need(not m.diagnostic(stdout+stderr,'warning') and not m.diagnostic(stdout+stderr,'error') and 'sorryAx' not in stdout+stderr,'diagnostic')
 names=['positive_bridge','byte_positive_bridge','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency'];reports={}
 for name in names:
  q=re.escape('Absorb89IPRAEndpoint.'+name);matches=re.findall(r"^'"+q+r"' depends on axioms: \[([^\]]*)\]$",stdout,re.M);empty=re.findall(r"^'"+q+r"' does not depend on any axioms$",stdout,re.M)
  need(len(matches)+len(empty)==1,'axiom report '+name);axioms=[] if empty else [x.strip() for x in matches[0].split(',') if x.strip()];need(set(axioms)<={'propext','Classical.choice','Quot.sound'},'axioms '+name);reports[name]=axioms
 need(obj.is_file(),'missing output');result['object_record']=m.rec(obj);result['axioms']=reports
 expected=dict(initial)
 for suffix in m.SUFFIXES:
  record=m.rec(str(obj)[:-len('.olean')]+suffix)
  if record is not None:expected['Absorb89IPRAEndpoint'+suffix]=record
 need(snapshot()==expected,'unexpected union mutation');guard_records()
 known=set(json.loads(m.INVENTORY.read_text())['objects'])|set(old['post_headers']['project'])|set(c['project'])|{'Absorb89IPRAEndpoint'}
 post=m.scan_closure(['Absorb89IPRAEndpoint'],[out],env,OBS,'post',known)
 allowed=set(old['post_headers']['project'])|set(c['project'])|{'Absorb89IPRAEndpoint'}
 need(set(post['project'])<=allowed,'unverified project imports '+str(set(post['project'])-allowed))
 need(not ({'FreeJRootBinding','FreeJSignedTransport'}&set(post['project'])),'namespace collision')
 for n,row in post['project'].items():
  if n=='Absorb89IPRAEndpoint':need(row['record']==result['object_record'],'new object drift');continue
  source=c['project'].get(n,old['post_headers']['project'].get(n));need(source is not None,'unverified '+n)
  for suf in m.SUFFIXES:
   a=row['companions'][suf];b=source['companions'][suf]
   need((None if a is None else a['sha256'])==(None if b is None else b['sha256']),'post object mismatch '+n+suf)
 for n,row in post['outside'].items():
  oldrow=c['outside'].get(n,old['post_headers']['outside'].get(n));need(oldrow==row,'unverified outside import '+n)
 m.recheck_outside(post);guard_records();need(snapshot()==expected,'union changed after scan')
 need(sha(copy)==sha(OBS/'source.lean')==SOURCE_PIN and sha(__file__)==result['runner_sha256'],'source or runner drift')
 result.update(status='PASS',post_headers=post,source_sha256=SOURCE_PIN)
except Exception as e:result.update(error=repr(e),traceback=traceback.format_exc())
(OBS/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':result['status'],'error':result.get('error'),'output_root':str(temp)}))
if result['status']!='PASS':sys.exit(1)
