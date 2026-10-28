from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
name='arithmetic-command-replaceperm222';latest=Path('/tmp/'+name+'-author-location.txt')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def recheck(i):
 for e in i['pins']:check(e)
if sys.argv[1]=='prepare':
 packet=V/'arithmetic-command-evaluationperm222-peer-replay.json';assert sha(packet)=='baea3f0577882c022af0dbd3177da13eb0fed10df472894b2d7432ae40932218'
 d=json.loads(packet.read_text());assert d['status']=='PASS';check(d['inputs']);i=json.loads(Path(d['inputs']['path']).read_text());pool={e['module']:e for e in i['modules']};external_names=set();seen=set();records=[]
 def visit(n):
  if n in seen:return
  seen.add(n)
  if n not in pool:external_names.add(n);return
  e=pool[n]
  for dep in e['imports']:visit(dep)
  records.append(e)
 visit('DiophantineConsistency.ArithmeticCommandStepPerm222')
 external=[e for e in i['external']if e['module']in external_names];assert {e['module']for e in external}==external_names
 assert len(records)==107 and len(external)==37
 assert shutil.disk_usage('/tmp').free>=512*1024**2
 p=Path(tempfile.mkdtemp(prefix=name+'-root-author-'));lib=p/'lib';lib.mkdir();pins=[rec(packet),d['inputs'],d['driver'],d['bundle_manifest'],*i['pins']]
 for e in records:
  pins.append(dict(path=e['source'],sha256=e['source_sha256']))
  for o in e['objects']:
   pins.append(o);q=lib/Path(*e['module'].split('.')[:-1])/Path(o['path']).name;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(o['path'])
 n=dict(status='AUTHENTICATED_BEFORE_EXECUTION',private=str(p),modules=records,external=external,pins=pins,compiler=i['compiler'],lean_path=':'.join([str(lib),*i['lean_path'].split(':')[1:]]),driver=rec(__file__),scope='Only two new actual C222 raw-command tail replacement leaves fresh over107 authenticated prerequisites. Actual IOpen effects, no Foundation build, append/compiler or HA consistency claim.')
 recheck(n);save(p/'inputs.json',n);latest.write_text(str(p));print(json.dumps(dict(private=str(p),cached=len(records),foundation=sum(r['module'].startswith('Foundation.')for r in records),artifacts=sum(len(r['objects'])for r in records),external=len(external),pins=len(pins)),indent=2))
elif sys.argv[1]=='compile':
 p=Path(latest.read_text());i=json.loads((p/'inputs.json').read_text());check(i['driver']);recheck(i);attempt=p/('attempt-'+str(time.time_ns()));attempt.mkdir();env=dict(os.environ,LEAN_PATH=i['lean_path'],LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);results=[]
 for suffix in ['', 'Checks']:
  n='DiophantineConsistency.ArithmeticCommandReplacePerm222'+suffix;source=R/'Computability/DiophantineConsistency/Lean'/Path(*n.split('.')).with_suffix('.lean');snapshot=attempt/(n+'.lean');shutil.copyfile(source,snapshot)
  assert shutil.disk_usage('/tmp').free>=512*1024**2
  out=p/'lib'/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.is_symlink();log=attempt/(n+'.txt');timing=attempt/(n+'.time');cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(source)];start=time.time()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  e=dict(module=n,source=rec(source),snapshot=rec(snapshot),command=cmd,exit_code=code,seconds=time.time()-start,log=rec(log),timing=rec(timing),object=rec(out)if code==0 else None);results.append(e);save(attempt/'RESULT.json',dict(records=results,status='PASS'if code==0 and suffix else'INCOMPLETE'));print(json.dumps(e),flush=True)
  if code:raise SystemExit(code)
 recheck(i)
 for e in results:check(e['source'])
 print('PASS '+str(attempt),flush=True)
else:raise SystemExit('prepare or compile')
