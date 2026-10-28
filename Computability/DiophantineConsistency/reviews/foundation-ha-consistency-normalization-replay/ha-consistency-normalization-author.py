from pathlib import Path
import json,hashlib,os,re,shutil,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';V=D/'reviews';A=D/'research/ha-fixed-consistency-normalization-proposal-pins.json';MARK=Path('/tmp/ha-consistency-normalization-author-location.txt')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def imports(p):
 text=Path(p).read_text();text=re.sub(r'/\-.*?\-/','',text,flags=re.S)
 return list(dict.fromkeys(['Init']+[n for line in re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',text,re.M)for n in line.split('--',1)[0].split()]))
NAMES=['FoundationHAConsistencyNormalization','FoundationHAConsistencyNormalizationChecks']
if sys.argv[1]=='prepare':
 assert sha(A)=='09ac7c3ac5e3e3694bbca03abb46d1bbdb1626b28c9c694eb8a8cb3a476a9a5e';a=json.loads(A.read_text());check(a['note']);modules=a['modules'];external=a['external'];assert len(modules)==455 and sum(e['module'].startswith('Foundation.')for e in modules)==139 and sum(len(e['objects'])for e in modules)==872 and len(external)==57
 pins=[rec(A),a['note'],a['compiler'],rec(__file__),rec(R/'lean-toolchain'),rec(R/'lake-manifest.json'),*a['pins']]
 for e in modules:
  assert sha(e['source'])==e['source_sha256'];assert set(imports(e['source']))==set(e['imports']),e['module'];assert not any('FoundationHAConsistencyNormalization'in n for n in e['imports'])
  pins.append(dict(path=e['source'],sha256=e['source_sha256']));pins.extend(e['objects'])
 for e in external:
  if e.get('source'):pins.append(e['source'])
  pins.extend(e['objects'])
 for e in pins:check(e)
 p=Path(tempfile.mkdtemp(prefix='ha-consistency-normalization-root-author-'));lib=p/'lib';lib.mkdir()
 assert shutil.disk_usage('/tmp').free>=512*1024**2
 for e in modules:
  for o in e['objects']:
   q=lib/Path(*e['module'].split('.')[:-1])/Path(o['path']).name;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(o['path'])
 parent=json.loads((V/'foundation-ha-zfc-validator-replay.json').read_text());check(parent['inputs']);pi=json.loads(Path(parent['inputs']['path']).read_text());paths=pi['lean_path'].split(':')[1:];assert all('/.lake/packages/'in x or '/toolchains/'in x for x in paths)
 i=dict(modules=modules,external=external,pins=pins,compiler=a['compiler'],lean_path=':'.join([str(lib),*paths]),counts=a['fixed_closure'],snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip());save(p/'inputs.json',i);MARK.write_text(str(p));print(json.dumps(dict(status='PREPARED',private=str(p),pins=len(pins))))
else:
 p=Path(MARK.read_text());i=json.loads((p/'inputs.json').read_text());attempt=p/('attempt-'+str(time.time_ns()));attempt.mkdir();lib=p/'lib';env=dict(os.environ,LEAN_PATH=i['lean_path'],LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 s=dict(status='RUNNING',inputs=rec(p/'inputs.json'),driver=rec(__file__),private=str(p),records=[]);save(attempt/'RESULT.json',s)
 for e in i['pins']:check(e)
 for name in NAMES:
  assert shutil.disk_usage('/tmp').free>=512*1024**2
  source=D/'Lean/DiophantineConsistency'/(name+'.lean');assert imports(source)==['Init',*(['DiophantineConsistency.FoundationHASigmaOneGG','DiophantineConsistency.FoundationHACurrentTransfer','DiophantineConsistency.FoundationZFCConsistencyNat']if name==NAMES[0]else['DiophantineConsistency.'+NAMES[0]])]
  snapshot=attempt/(name+'.lean');shutil.copyfile(source,snapshot);out=lib/'DiophantineConsistency'/(name+'.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.is_symlink()
  if out.exists():shutil.copyfile(out,attempt/(name+'.previous.olean'))
  log=attempt/(name+'.log');timing=attempt/(name+'.time');cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(source)];start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  x=dict(module='DiophantineConsistency.'+name,source=rec(source),snapshot=rec(snapshot),command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing),object=rec(out)if code==0 else None);s['records'].append(x);save(attempt/'RESULT.json',s);print(json.dumps(x),flush=True)
  assert sha(source)==sha(snapshot)
  if code:s['status']='FAILED';save(attempt/'RESULT.json',s);print(log.read_text(),flush=True);raise SystemExit(code)
  reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());x['axiom_reports']=reports
  for name,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
  assert not re.search(r'\b(?:warning|error):',log.read_text())
 for e in i['pins']:check(e)
 assert Path(s['records'][0]['log']['path']).read_text()=='' and len(s['records'][1]['axiom_reports'])==8
 s['status']='PASS';save(attempt/'RESULT.json',s);save(p/'LATEST.json',rec(attempt/'RESULT.json'));print(json.dumps(dict(status='PASS',private=str(p),result=str(attempt/'RESULT.json'))),flush=True)
