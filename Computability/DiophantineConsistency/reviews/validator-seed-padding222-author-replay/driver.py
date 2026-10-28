from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
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
ap=D/'research/validator-source-derivation222-plan.json'
bp=D/'reviews/validator-seed-image222-root-replay/packet.json'
rp=D/'reviews/validator-seed-image222-root-replay/ROOT.json'
cp=D/'reviews/validator-source-quantifier-context222-cache.json'
assert sha(ap)=='9dc83e9ab42279fd86c004c171609a54c228703f922fafe458bba33f177f66ba'
a=json.loads(ap.read_text());b=json.loads(bp.read_text())['inputs'];c=json.loads(cp.read_text())
modules={x['module']:x for x in b['modules']}
for x in a['modules']:
 if x['module']in modules:
  old=modules[x['module']]
  assert old['source_sha256']==x['source_sha256']
  assert old['objects'][0]['sha256']==x['objects'][0]['sha256']
 modules[x['module']]=x
sr=json.loads(rp.read_text())['state']['completed'][0]
assert sr['module']=='ZFCinPA.ValidatorSeedImage222'and sr['matches_author']
modules[sr['module']]=dict(module=sr['module'],source=sr['source'],source_sha256=sr['source_sha256'],
 objects=[dict(path=sr['object'],sha256=sr['object_sha256'])],imports=['Init','ZFCinPA.ValidatorSeedClosure222'],
 provenance='Accepted independent SeedImage root replay; direct source/current dependency overlap agrees')
roots=['ZFCinPA.ValidatorSeedImage222','ZFCinPA.ValidatorEnvironmentStreams222'];done=set();active=set();order=[];external=set()
def visit(n):
 if n not in modules:external.add(n);return
 if n in done:return
 assert n not in active,n
 active.add(n)
 for dep in modules[n]['imports']:visit(dep)
 active.remove(n);done.add(n);order.append(n)
for n in roots:visit(n)
mods=[modules[n]for n in order];extmap={x['module']:x for x in a['external']}
assert external<=extmap.keys()
ext=[extmap[n]for n in sorted(external)]
assert len(mods)==160 and sum(x['module'].startswith('Foundation.')for x in mods)==117
assert sum(len(x['objects'])for x in mods)==511 and len(ext)==40
pins=[rec(ap),rec(bp),rec(rp),rec(cp),rec(__file__),rec(D/'reviews/validator-seed-image222-root.md'),rec(D/'reviews/validator-seed-image222-peer.md'),rec(D/'research/c222-seed-padding-plan-20261026.md')]
for k in ['compiler','manifest','toolchain']:pins.append(dict(path=c[k],sha256=c[k+'_sha256']))
for m in mods:
 assert imports(m['source'])==list(dict.fromkeys(m['imports'])),m['module']
 pins.append(dict(path=m['source'],sha256=m['source_sha256']));pins.extend(m['objects'])
pins.extend(dict(path=x['path'],sha256=x['sha256'])for x in ext)
for x in pins:check(x)
assert shutil.disk_usage('/tmp').free>=512*1024**2
p=Path(tempfile.mkdtemp(prefix='seed-padding222-root-author-'));lib=p/'lib';lib.mkdir()
for m in mods:
 for x in m['objects']:
  dest=lib/Path(*m['module'].split('.')[:-1])/Path(x['path']).name
  dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();dest.symlink_to(x['path'])
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*c['lean_path'].split(':')[1:]]),LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH',None)
inputs=dict(modules=mods,external=ext,pins=pins,counts=dict(cached=160,foundation=117,artifacts=511,boundaries=40),
 compiler=dict(path=c['compiler'],sha256=c['compiler_sha256']),lean_path=env['LEAN_PATH'],direct_imports=roots)
save(p/'inputs.json',inputs)
state=dict(status='RUNNING',inputs=rec(p/'inputs.json'),driver=rec(__file__),private=str(p),records=[])
save(p/'AUTHOR.json',state)
marker=Path('/tmp/seed-padding222-root-author-attempts.json')
attempts=json.loads(marker.read_text())if marker.exists()else[]
attempts.append(str(p));save(marker,attempts)
print('PREPARED '+str(p),flush=True)
for n in ['ValidatorSeedPadding222','ValidatorSeedPadding222Checks']:
 assert shutil.disk_usage(p).free>=512*1024**2
 src=R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA'/(n+'.lean');snap=p/src.name;shutil.copyfile(src,snap)
 module='ZFCinPA.'+n;out=lib/'ZFCinPA'/(n+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 assert not out.exists()and not out.is_symlink()
 log=p/(n+'.log');timing=p/(n+'.time');cmd=[c['compiler'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)]
 start=time.monotonic()
 with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 row=dict(module=module,source=rec(src),snapshot=rec(snap),command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing))
 state['records'].append(row);save(p/'AUTHOR.json',state)
 if code:
  state['status']='FAILED';save(p/'AUTHOR.json',state);print(log.read_text());raise SystemExit(code)
 assert sha(src)==sha(snap)and not out.is_symlink()
 row['object']=rec(out)
 reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())
 row['axiom_reports']=reports
 assert not re.search(r'\b(?:error|warning):|sorryAx',log.read_text())
 for _,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
 save(p/'AUTHOR.json',state);print(json.dumps(dict(module=module,seconds=row['seconds'],reports=len(reports))),flush=True)
for x in pins:check(x)
assert sum(len(x['axiom_reports'])for x in state['records'])==11
state['status']='PASS';save(p/'AUTHOR.json',state);print('PASS '+str(p),flush=True)
