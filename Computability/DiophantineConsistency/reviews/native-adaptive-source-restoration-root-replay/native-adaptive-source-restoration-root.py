from pathlib import Path
import json,hashlib,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
V=R/'Computability/DiophantineConsistency/reviews'
mp=V/'native-adaptive-source-restoration-replay.json'
def sha(f):return hashlib.sha256(Path(f).read_bytes()).hexdigest()
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def rec(f):return dict(path=str(f),sha256=sha(f))
def save(f,d):f.write_text(json.dumps(d,indent=2)+'\n')
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
 lines=re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(out),re.M)
 return list(dict.fromkeys(['Init']+[n for line in lines for n in line.split()]))
assert sha(mp)=='3228854d5e430585198928063a65b647acf5f8b8b73749d49af3bcb8108dd4d0'
d=json.loads(mp.read_text());assert d['status']=='PASS'
assert len(d['artifact_texts'])==32
i=d['inputs'];custom=i['selected_custom'];external=i['external_boundary']
assert len(custom)==33 and len(external)==22
assert sum(len(e['artifacts'])for e in external)==66
pins=[rec(mp),rec(V/'native-adaptive-source-restoration-author.md'),rec(__file__),d['driver'],d['inputs_record'],d['state_record'],d['manifest'],*d['artifact_texts'],*i['pins']]
names={e['module']for e in custom};boundary={e['module']for e in external}
assert len(names)==33 and len(boundary)==22 and not names&boundary
for e in custom:
 pins.extend([e['source'],e['object']])
 actual=imports(e['source']['path'])
 assert actual==list(dict.fromkeys(e['actual_imports'])),e['module']
 assert set(actual)<=names|boundary,e['module']
for e in external:pins.extend([e['source'],*e['artifacts']])
for e in d['completed']:
 for k in ['source','snapshot','log','timing','object']:pins.append(e[k])
 assert set(imports(e['source']['path']))<=names|boundary|{x['module']for x in d['completed']}
for e in pins:check(e)
assert shutil.disk_usage('/tmp').free>=512*1024**2
p=Path(tempfile.mkdtemp(prefix='native-adaptive-source-restoration-root-'));lib=p/'lib';lib.mkdir()
for e in custom:
 q=lib/Path(*e['module'].split('.')).with_suffix('.olean')
 q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(e['object']['path'])
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*i['LEAN_PATH'][1:]]),LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH',None)
s=dict(status='RUNNING',private=str(p),author_packet=rec(mp),driver=rec(__file__),pins=pins,records=[],counts=dict(custom=33,external=22,external_companions=66))
save(p/'ROOT.json',s);Path('/tmp/native-adaptive-source-restoration-root-location.txt').write_text(str(p))
for e in d['completed']:
 assert shutil.disk_usage(p).free>=512*1024**2
 check(e['source'])
 n=e['module'];src=Path(e['source']['path']);snap=p/src.name;shutil.copyfile(src,snap)
 out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 assert not out.exists()and not out.is_symlink()
 log=p/(n+'.txt');timing=p/(n+'.time')
 cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)]
 start=time.monotonic()
 with log.open('w')as f:
  code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 x=dict(module=n,source=e['source'],snapshot=rec(snap),command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing),object=rec(out)if code==0 else None)
 s['records'].append(x);save(p/'ROOT.json',s)
 assert code==0,log.read_text()
 assert not out.is_symlink()and sha(src)==sha(snap)
 x['matches_author']=x['object']['sha256']==e['object']['sha256'];assert x['matches_author']
 reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())
 x['axiom_reports']=reports
 for title,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(?:error|warning):|sorryAx',log.read_text())
 save(p/'ROOT.json',s);print(json.dumps(dict(module=n,seconds=x['seconds'],matches_author=True,reports=len(reports))),flush=True)
for e in pins:check(e)
assert len(s['records'])==2 and sum(len(e['axiom_reports'])for e in s['records'])==5
assert Path(s['records'][0]['log']['path']).read_text()==''
s['status']='PASS';save(p/'ROOT.json',s);print('PASS '+str(p),flush=True)
