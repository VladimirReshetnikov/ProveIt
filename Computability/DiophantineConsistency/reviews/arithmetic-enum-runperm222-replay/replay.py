from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
name='arithmetic-enum-runperm222';latest=Path('/tmp/'+name+'-author-location.txt')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def recheck(i):
 for e in i['pins']:check(e)
if sys.argv[1]=='prepare':
 parents=[V/'arithmetic-enum-stepperm222-replay.json',V/'arithmetic-enum-stepperm222-root-replay/ROOT.json',V/'validator-atomic-transport222-replay.json',R/'lake-manifest.json']
 expected=['baa28c4880dac35ce88a58d6b99a571069c331357775b2a0301b6615676f200d','558947f7ca74a4aad47ca8309b093e3f884b921655bfde85f8136f1e3eee19fd','ce6ba2f8a7ea620fc6ddd532eca189afc41fba7fe1d68a84d4e7ff11035baf9f']
 for p,h in zip(parents,expected):assert sha(p)==h
 ed=json.loads(parents[0].read_text());check(ed['inputs']);ei=json.loads(Path(ed['inputs']['path']).read_text());a=json.loads(parents[2].read_text())['inputs'];s=json.loads(parents[1].read_text());assert s['status']=='PASS'
 records={e['module']:e for e in a['modules']}
 for e in ei['modules']:
  if e['module']in records:assert e['source_sha256']==records[e['module']]['source_sha256']
  records[e['module']]=e
 e=s['records'][0];assert e['module']=='DiophantineConsistency.ArithmeticEnumStepPerm222'
 records[e['module']]=dict(module=e['module'],source=e['source']['path'],source_sha256=e['source']['sha256'],objects=[e['object']],provenance='accepted independent root fresh enumerator-step primary')
 external={e['module']:e for e in a['external']}
 for r in ei['external']:
  e=dict(module=r['module'],**r['object'])
  if e['module']in external:assert e['sha256']==external[e['module']]['sha256']
  external[e['module']]=e
 needed=set();boundary=set()
 def visit(n):
  if n in needed or n in boundary:return
  if n in external:boundary.add(n);return
  assert n in records,('missing custom module',n)
  e=records[n];assert sha(e['source'])==e['source_sha256']
  for o in e['objects']:check(o)
  imports=['Init']+[t for line in re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',Path(e['source']).read_text(),re.M)for t in line.split('--',1)[0].split()]
  e['imports']=imports;needed.add(n)
  for m in imports:visit(m)
 visit('DiophantineConsistency.ArithmeticEnumStepPerm222');visit('Foundation.FirstOrder.Arithmetic.HFS.PRF')
 assert shutil.disk_usage('/tmp').free>=512*1024**2
 p=Path(tempfile.mkdtemp(prefix=name+'-root-author-'));lib=p/'lib';lib.mkdir();pins=[rec(q)for q in parents]+[ed['inputs'],ei['compiler']]
 for n in sorted(needed):
  e=records[n];pins.append(dict(path=e['source'],sha256=e['source_sha256']))
  for o in e['objects']:
   pins.append(o);q=lib/Path(*n.split('.')[:-1])/Path(o['path']).name;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(o['path'])
 for n in sorted(boundary):pins.append(external[n])
 i=dict(status='AUTHENTICATED_BEFORE_EXECUTION',private=str(p),modules=[records[n]for n in sorted(needed)],external=[external[n]for n in sorted(boundary)],pins=pins,compiler=ei['compiler'],lean_path=':'.join([str(lib),*ei['lean_path'].split(':')[1:]]),driver=rec(__file__),scope='Only two new run leaves fresh; reuse the authenticated exact step closure and cached PRF subset. No Foundation build. No scheduler fairness, proof invariant, exact215 simulation or HA consistency equivalence.')
 recheck(i);save(p/'inputs.json',i);latest.write_text(str(p));print(json.dumps(dict(private=str(p),cached=len(needed),foundation=sum(n.startswith('Foundation.')for n in needed),artifacts=sum(len(records[n]['objects'])for n in needed),external=len(boundary),pins=len(pins),inputs=rec(p/'inputs.json')),indent=2))
elif sys.argv[1]=='compile':
 p=Path(latest.read_text());i=json.loads((p/'inputs.json').read_text());check(i['driver']);recheck(i);attempt=p/('attempt-'+str(time.time_ns()));attempt.mkdir();env=dict(os.environ,LEAN_PATH=i['lean_path'],LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);results=[]
 for suffix in ['', 'Checks']:
  n='DiophantineConsistency.ArithmeticEnumRunPerm222'+suffix;source=R/'Computability/DiophantineConsistency/Lean'/Path(*n.split('.')).with_suffix('.lean');snapshot=attempt/(n+'.lean');shutil.copyfile(source,snapshot)
  assert shutil.disk_usage('/tmp').free>=512*1024**2
  out=p/'lib'/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.is_symlink();log=attempt/(n+'.txt');timing=attempt/(n+'.time');cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(source)];start=time.time()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  e=dict(module=n,source=rec(source),snapshot=rec(snapshot),command=cmd,exit_code=code,seconds=time.time()-start,log=rec(log),timing=rec(timing),object=rec(out)if code==0 else None);results.append(e);save(attempt/'RESULT.json',dict(records=results,status='PASS'if code==0 and suffix else'INCOMPLETE'));print(json.dumps(e),flush=True)
  if code:raise SystemExit(code)
 recheck(i)
 for e in results:check(e['source'])
 print('PASS '+str(attempt),flush=True)
else:raise SystemExit('prepare or compile')
