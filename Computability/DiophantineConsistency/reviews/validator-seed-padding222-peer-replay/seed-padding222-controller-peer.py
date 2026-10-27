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
packet=D/'reviews/validator-seed-padding222-replay.json';receipt=D/'reviews/validator-seed-padding222-author.md'
assert sha(packet)=='7e789439d2947be695cefef69378da3d1426c0b5298be5afd30dc86b5e45c228'
assert sha(receipt)=='b2e8a00821cfd134452f537d22624facf9204a537b273af54dbd4a9f00053031'
a=json.loads(packet.read_text());check(a['inputs']);x=json.loads(Path(a['inputs']['path']).read_text())
assert x['counts']==dict(cached=160,foundation=117,artifacts=511,boundaries=40)
pins=[rec(packet),rec(receipt),rec(__file__),a['inputs'],a['driver'],a['bundle_manifest'],*a['attempts'],*x['pins']]
manifest=Path(a['bundle_manifest']['path']);m=json.loads(manifest.read_text());assert len(m)==31
for e in m:
 pins.append(dict(path=str(manifest.parent/e['path']),sha256=e['sha256']))
 pins.append(dict(path=e['original'],sha256=e['sha256']))
for row in a['records']:
 for key in ['source','snapshot','object','log','timing']:pins.append(row[key])
mods={v['module']:v for v in x['modules']};bound={v['module']for v in x['external']}
assert len(mods)==160 and sum(n.startswith('Foundation.')for n in mods)==117
assert sum(len(v['objects'])for v in mods.values())==511 and len(bound)==40
seen=set();visiting=set();external=set()
def visit(n):
 if n not in mods:external.add(n);return
 if n in seen:return
 assert n not in visiting
 visiting.add(n);v=mods[n];assert imports(v['source'])==list(dict.fromkeys(v['imports'])),n
 for dep in v['imports']:visit(dep)
 visiting.remove(n);seen.add(n)
for n in x['direct_imports']:visit(n)
assert seen==set(mods)and external==bound
assert all(r['module']not in mods for r in a['records'])
for p in pins:check(p)
assert shutil.disk_usage('/tmp').free>=512*1024**2
p=Path(tempfile.mkdtemp(prefix='seed-padding222-controller-peer-'));lib=p/'lib';lib.mkdir()
for n,v in mods.items():
 for o in v['objects']:
  dst=lib/Path(*n.split('.')[:-1])/Path(o['path']).name
  dst.parent.mkdir(parents=True,exist_ok=True);assert not dst.exists();dst.symlink_to(o['path'])
paths=x['lean_path'].split(':')[1:]
assert all('/.lake/packages/'in t for t in paths)
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*paths]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
inputs=dict(author_packet=rec(packet),author_inputs=a['inputs'],modules=x['modules'],external=x['external'],pins=pins,counts=x['counts'],compiler=x['compiler'],lean_path=env['LEAN_PATH'],source_imports_verified=True)
save(p/'inputs.json',inputs)
state=dict(status='RUNNING',inputs=rec(p/'inputs.json'),driver=rec(__file__),private=str(p),records=[],counts=x['counts'],pin_observations=len(pins),scope='Two independent fresh leaves only; complete selected input and author evidence authentication; no prerequisite rebuild.')
save(p/'PEER.json',state);Path('/tmp/seed-padding222-controller-peer-location.txt').write_text(str(p)+'\n');print('PREPARED '+str(p),flush=True)
for author in a['records']:
 assert shutil.disk_usage(p).free>=512*1024**2
 src=Path(author['source']['path']);assert imports(src)==(['Init',*x['direct_imports']]if author is a['records'][0]else['Init',a['records'][0]['module']])
 snap=p/src.name;shutil.copyfile(src,snap);out=lib/Path(*author['module'].split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 assert not out.exists()and not out.is_symlink()
 log=p/(src.stem+'.log');timing=p/(src.stem+'.time');cmd=[x['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)]
 start=time.monotonic()
 with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 row=dict(module=author['module'],source=rec(src),snapshot=rec(snap),command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing))
 state['records'].append(row);save(p/'PEER.json',state)
 if code:
  state['status']='FAILED';save(p/'PEER.json',state);print(log.read_text());raise SystemExit(code)
 assert sha(src)==sha(snap)==author['source']['sha256']and not out.is_symlink()
 row['object']=rec(out);row['matches_author']=sha(out)==author['object']['sha256'];assert row['matches_author']
 reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());row['axiom_reports']=reports
 assert reports==[tuple(r)for r in author['axiom_reports']]
 assert not re.search(r'\b(?:error|warning):|sorryAx',log.read_text())
 for _,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
 save(p/'PEER.json',state);print(json.dumps(dict(module=row['module'],seconds=row['seconds'],reports=len(reports),matches_author=True)),flush=True)
for q in pins:check(q)
assert sum(len(r['axiom_reports'])for r in state['records'])==11
state['status']='PASS';save(p/'PEER.json',state);print('PASS '+str(p),flush=True)
