from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';name=sys.argv[1];expected=sys.argv[2];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
mp=V/(name+'-replay.json');assert sha(mp)==expected;d=json.loads(mp.read_text());check(d['inputs']);i=json.loads(Path(d['inputs']['path']).read_text());p=Path(tempfile.mkdtemp(prefix=name+'-root-peer-'));lib=p/'lib';lib.mkdir();pins=[rec(mp),d['inputs'],d['driver'],*i['pins'],i['compiler']];names={e['module']for e in d['records']}
for e in i['modules']:
 assert e['module']not in names;assert sha(e['source'])==e['source_sha256'];pins.append(dict(path=e['source'],sha256=e['source_sha256']))
 for o in e['objects']:
  check(o);pins.append(o);q=lib/Path(*e['module'].split('.')[:-1])/Path(o['path']).name;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(o['path'])
for e in d['records']:
 for k in ['source','snapshot','log','object']:check(e[k]);pins.append(e[k])
for e in pins:check(e)
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib),*i['lean_path'].split(':')[1:]]);env.pop('LEAN_SRC_PATH',None);s=dict(status='RUNNING',private=str(p),name=name,driver=rec(__file__),author_record=rec(mp),cached_count=len(i['modules']),pins=pins,records=[]);save(p/'ROOT.json',s);Path('/tmp/'+name+'-root-location.txt').write_text(str(p))
for e in d['records']:
 assert shutil.disk_usage(p).free>=512*1024**2;check(e['source']);n=e['module'];out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists()and not out.is_symlink();log=p/(n+'.txt');cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),e['source']['path']];start=time.time()
 with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 x=dict(module=n,source=e['source'],command=cmd,exit_code=code,seconds=time.time()-start,log=rec(log),object=rec(out)if code==0 else None);s['records'].append(x);save(p/'ROOT.json',s);print(json.dumps(x),flush=True)
 if code:s['status']='FAILED';save(p/'ROOT.json',s);raise SystemExit(code)
 reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());x['axiom_reports']=reports;x['matches_author']=x['object']['sha256']==e['object']['sha256'];save(p/'ROOT.json',s)
 for title,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},title
 assert not re.search(r'\b(?:error|warning):',log.read_text()),n
for e in pins:check(e)
s['status']='PASS';save(p/'ROOT.json',s);print('PASS '+str(p),flush=True)
