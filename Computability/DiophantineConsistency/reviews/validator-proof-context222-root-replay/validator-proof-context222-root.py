from pathlib import Path
import json,hashlib,re,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
P=V/'validator-proof-context222-replay.json';CACHE=V/'validator-proof-context222-cache.json'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
assert sha(P)=='0c0a194536c1d10633838ee69c258d5eef0dfb5105bea5ffb0b03f55103ff65c'
assert sha(CACHE)=='1291c1b923dd64dcebcb323cec22cde4d5afb437d830f9b315ee2792c15b4dd4'
a=json.loads(P.read_text());i=a['inputs'];assert a['status']=='PASS'
assert json.loads(CACHE.read_text())==i
mods=i['modules'];assert len(mods)==152 and sum(m['module'].startswith('Foundation.')for m in mods)==117
assert sum(len(m['objects'])for m in mods)==503 and len(i['external'])==39
pins=[rec(P),rec(CACHE),rec(__file__),rec(V/'validator-proof-context222-author.md')]
for k in ['compiler','manifest','toolchain']:pins.append(dict(path=i[k],sha256=i[k+'_sha256']))
pins.extend(i['parent_receipts'])
external_plan=V.parent/'research/c222-refutation-execution-cache-plan-20261026.json'
assert sha(external_plan)=='9b9a856c68329531594024c2ba503f39fd011183a58cf8d7bc40d93c1b353f06'
aesop=next(e for e in json.loads(external_plan.read_text())['external']if e['module']=='Aesop')
pins.extend([rec(external_plan),aesop])
normalizations=[]
for m in mods:
 actual=list(dict.fromkeys(['Init']+[n for line in re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',Path(m['source']).read_text(),re.M)for n in line.split('--',1)[0].split()]))
 recorded=list(dict.fromkeys(m['imports']))
 if actual!=recorded:
  assert m['module']=='Foundation.FirstOrder.Basic.AesopInit'
  assert recorded==['Init','Aesop.Frontend.Command']and actual==['Init','Aesop','Aesop.Frontend.Command']
  normalizations.append(dict(module=m['module'],recorded=recorded,actual=actual,added_boundary=aesop))
 else:assert actual==recorded,m['module']
 pins.append(dict(path=m['source'],sha256=m['source_sha256']));pins.extend(m['objects'])
pins.extend(i['external']);bundle=Path(a['bundle']);manifest=bundle/'FILES.json';assert sha(manifest)==a['manifest_sha256'];pins.append(rec(manifest))
for e in json.loads(manifest.read_text()):pins.append(dict(path=str(bundle/e['path']),sha256=e['sha256']))
for e in a['completed']:
 for k in ['source','snapshot','log','timing']:pins.append(dict(path=e[k],sha256=e[k+'_sha256']))
 pins.append(e['object'])
for e in pins:check(e)
p=Path(tempfile.mkdtemp(prefix='validator-proof-context222-root-peer-'));lib=p/'lib';lib.mkdir()
for m in mods:
 for o in m['objects']:
  q=lib/Path(*m['module'].split('.')[:-1])/Path(o['path']).name;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(o['path'])
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*i['lean_path'].split(':')[1:]]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
assert len(normalizations)==1
s=dict(status='RUNNING',private=str(p),author_record=rec(P),driver=rec(__file__),pins=pins,records=[],counts=dict(cached=152,foundation=117,artifacts=503,boundaries=40),original_author_counts=i['counts'],import_normalizations=normalizations);save(p/'ROOT.json',s);Path('/tmp/validator-proof-context222-root-location.txt').write_text(str(p));print('PRIVATE '+str(p),flush=True)
for expected in a['completed']:
 assert shutil.disk_usage(p).free>=512*1024**2
 n=expected['module'];src=Path(expected['source']);out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists()and not out.is_symlink()
 log=p/(n+'.txt');timing=p/(n+'.time');cmd=[i['compiler'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];start=time.monotonic()
 with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 r=dict(module=n,source=rec(src),command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing),object=rec(out)if code==0 else None);s['records'].append(r);save(p/'ROOT.json',s);print(json.dumps(r),flush=True)
 assert code==0,log.read_text();assert not out.is_symlink();r['matches_author']=r['object']['sha256']==expected['object']['sha256'];assert r['matches_author']
 reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());r['axiom_reports']=reports
 for title,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(?:error|warning):|sorryAx',log.read_text())
for e in pins:check(e)
assert sum(len(e['axiom_reports'])for e in s['records'])==16 and Path(s['records'][0]['log']['path']).read_text()==''
s['status']='PASS';save(p/'ROOT.json',s);print('PASS '+str(p),flush=True)
