from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time,sys
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def check(x):assert sha(x['path'])==x['sha256'],x['path']
def imports(path):
 s=Path(path).read_text();out=[];j=0;depth=0
 while j<len(s):
  pair=s[j:j+2]
  if depth:
   if pair=='/-':depth+=1;out.extend('  ');j+=2
   elif pair=='-/':depth-=1;out.extend('  ');j+=2
   else:out.append('\n'if s[j]=='\n'else' ');j+=1
  elif pair=='/-':depth=1;out.extend('  ');j+=2
  elif pair=='--':
   while j<len(s)and s[j]!='\n':out.append(' ');j+=1
  else:out.append(s[j]);j+=1
 assert depth==0
 return list(dict.fromkeys(['Init']+[n for line in re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(out),re.M)for n in line.split()]))
ap=D/'research/c222-dagperm-control-cache-plan-20261026.json'
assert sha(ap)=='b3ecbe703da86e953c2e06ed1dcca7b9f6e40598d8a8d82b3563c408ed45d729'
a=json.loads(ap.read_text());mods={m['module']:m for m in a['modules']}
assert a['counts']==dict(custom=138,Foundation=95,reuse=137,artifacts=422,fresh_unchanged=1,external=39)
pins=[rec(ap),rec(__file__),*a['pins'],rec(D/'research/c222-dagperm-control-proposal-20261026.md'),rec('/tmp/build-dag-controlperm222-source.py')]
peer=Path('/tmp/arithmetic-dag-loops-peer-v9mmg0s_');verified=json.loads((peer/'VERIFIED.json').read_text());assert verified['status']=='PASS'
pins += [rec(peer/'VERIFIED.json'),rec(peer/'PEER.json'),rec(peer/'inputs.json'),rec(D/'reviews/arithmetic-dag-loops-peer.md'),rec(D/'reviews/arithmetic-dag-loops-peer-replay.json')]
changes=[]
for row in verified['records']:
 n=row['module']
 if n not in mods:continue
 assert row['exit_code']==0 and row['source']['sha256']==mods[n]['source']['sha256']
 obj=row['object'];assert obj['sha256']==mods[n]['objects'][0]['sha256']
 changes.append(dict(module=n,old_provider=mods[n]['objects'],new_provider=obj))
 mods[n]['objects']=[obj]
 for key in ['source','snapshot','object','log','timing']:pins.append(row[key])
assert len(changes)==7
for m in mods.values():
 assert imports(m['source']['path'])==m['imports'],m['module']
 pins.append(m['source']);pins.extend(m.get('objects',[]))
seen=set();external=set()
def visit(n):
 if n not in mods:external.add(n);return
 if n in seen:return
 seen.add(n)
 for i in mods[n]['imports']:visit(i)
for n in a['direct_imports']:visit(n)
assert seen==set(mods)and external=={e['module']for e in a['external']}
prior={}
if len(sys.argv)>1:
 old=Path(sys.argv[1]);state=json.loads((old/'AUTHOR.json').read_text());pins.append(rec(old/'AUTHOR.json'))
 for row in state['records']:
  if row['module']in a['refresh_order']:
   assert row['exit_code']==0 and row['source']==mods[row['module']]['source']
   prior[row['module']]=row['object'];pins.append(row['object'])
 assert set(prior)==set(a['refresh_order'])
for x in pins:check(x)
assert shutil.disk_usage('/tmp').free>=512*1024**2
p=Path(tempfile.mkdtemp(prefix='dag-controlperm222-controller-author-'));lib=p/'lib';lib.mkdir()
for n,m in mods.items():
 objects=m.get('objects',([prior[n]]if n in prior else[]))
 for o in objects:
  dest=lib/Path(*n.split('.')[:-1])/Path(o['path']).name
  dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();dest.symlink_to(o['path'])
base=json.loads(Path('/tmp/enum-soundnessperm222-controller-author-31ivs4am/inputs.json').read_text())
paths=base['lean_path'].split(':')[1:]
assert all('/.lake/packages/'in x or x=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'for x in paths)
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*paths]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
inputs=dict(cache=rec(ap),modules=list(mods.values()),external=a['external'],pins=pins,counts=a['counts'],compiler=a['compiler'],lean_path=env['LEAN_PATH'],prior_refreshed=prior,provider_supplement=dict(changes=changes,scope='Root directed selection of independent byte-identical peer objects; root final acceptance receipt/commit pending. Historical plan unchanged.'))
save(p/'inputs.json',inputs)
state=dict(status='RUNNING',inputs=rec(p/'inputs.json'),driver=rec(__file__),private=str(p),records=[],counts=a['counts'],pin_observations=len(pins))
save(p/'AUTHOR.json',state)
marker=Path('/tmp/dag-controlperm222-controller-author-attempts.json');attempts=json.loads(marker.read_text())if marker.exists()else[]
attempts.append(str(p));save(marker,attempts);print('PREPARED '+str(p),flush=True)
new=['BusyBeaver.ZFC.ArithmeticDagControlPerm222','BusyBeaver.ZFC.ArithmeticDagControlPerm222Checks']
for n in ([]if prior else a['refresh_order'])+new:
 assert shutil.disk_usage(p).free>=512*1024**2
 src=Path(mods[n]['source']['path'])if n in mods else R/'Computability/BusyBeaver/Lean'/Path(*n.split('.')).with_suffix('.lean')
 snap=p/src.name;shutil.copyfile(src,snap);out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 assert not out.exists()and not out.is_symlink()
 log=p/(src.stem+'.log');timing=p/(src.stem+'.time');cmd=[a['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)]
 start=time.monotonic()
 with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 row=dict(module=n,source=rec(src),snapshot=rec(snap),command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing))
 state['records'].append(row);save(p/'AUTHOR.json',state)
 if code:
  state['status']='FAILED';save(p/'AUTHOR.json',state);print(log.read_text());raise SystemExit(code)
 assert sha(src)==sha(snap)and not out.is_symlink()
 row['object']=rec(out)
 reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());row['axiom_reports']=reports
 assert not re.search(r'\b(?:error):|sorryAx',log.read_text())
 assert not re.search(r'\bwarning:',log.read_text())
 for _,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
 save(p/'AUTHOR.json',state);print(json.dumps(dict(module=n,seconds=row['seconds'],reports=len(reports))),flush=True)
for x in pins:check(x)
assert sum(len(r['axiom_reports'])for r in state['records']if r['module']in new)==11
state['status']='PASS';save(p/'AUTHOR.json',state);print('PASS '+str(p),flush=True)
