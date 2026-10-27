from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
packet=V/'native-shifted-source-adapter-replay.json';assert sha(packet)=='f1e956387698cec42c48568430e7056b0bed2854b519304a9afcb8b1784fe86d'
packetdata=json.loads(packet.read_text());assert packetdata['status']=='PASS';check(packetdata['run']['inputs']);i=json.loads(Path(packetdata['run']['inputs']['path']).read_text());assert len(i['selected_custom'])==365;d=dict(run=packetdata['artifacts'],source_files=i['sources'],driver=packetdata['run']['driver']);assert len(d['run'])==4
for e in packetdata['files']:
 assert hashlib.sha256(e['text'].encode()).hexdigest()==e['sha256'];check(e)
pins=[rec(packet),rec(R/'lake-manifest.json'),d['driver'],*i['pins']]
for e in d['run']:
 for k in ['snapshot','log','object']:check(e[k]);pins.append(e[k])
for e in pins:check(e)
p=Path(tempfile.mkdtemp(prefix='native-shifted-source-root-'));lib=p/'lib';lib.mkdir();Path('/tmp/native-shifted-source-root-location.txt').write_text(str(p))
fresh={e['module']for e in d['run']}
for r in i['selected_custom']:
 assert r['module']not in fresh
 for k in ['source','current_source','object']:check(r[k])
 assert r['source']['sha256']==r['current_source']['sha256'],r['module']
 q=lib/Path(*r['module'].split('.')).with_suffix('.olean');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(Path(r['object']['path']).resolve())
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*i['LEAN_PATH'][1:]]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
s=dict(status='RUNNING',scope='Independent four-leaf current-source native rebuild over365 authenticated cached prerequisites; no Foundation or whole-closure build.',private=str(p),driver=rec(__file__),packet=rec(packet),pins=pins,selected_custom=i['selected_custom'],LEAN_PATH=env['LEAN_PATH'],completed=[]);save(p/'ROOT.json',s)
try:
 for a in d['run']:
  assert shutil.disk_usage(p).free>=512*1024**2;source=next(e for e in d['source_files']if e['module']==a['module']);check(source);n=a['module'];out=lib/Path(*n.split('.')).with_suffix('.olean');assert not out.exists()and not out.is_symlink();out.parent.mkdir(parents=True,exist_ok=True);log=p/(n+'.txt');snapshot=p/(n+'.lean');shutil.copyfile(source['path'],snapshot);cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),source['path']];start=time.time()
  with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  e=dict(module=n,source=source,command=cmd,exit_code=code,seconds=time.time()-start,log=rec(log),snapshot=rec(snapshot),object=rec(out)if code==0 else None);s['completed'].append(e);save(p/'ROOT.json',s);print(json.dumps(e),flush=True);assert code==0
  raw=log.read_text();assert not re.search(r'\b(?:error|warning):',raw)
  reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",raw);expected={'DiophantineConsistency.SelectiveCertificate52':2,'DiophantineConsistency.NativeQuadraticParent':4,'DiophantineConsistency.NativeShiftedSourceAdapter':0,'DiophantineConsistency.NativeShiftedSourceAdapterChecks':12};assert len(reports)==expected[n]
  for title,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},title
  e['axiom_reports']=reports;e['matches_author']=e['object']['sha256']==a['object']['sha256'];check(source);save(p/'ROOT.json',s)
 for e in pins:check(e)
 s['status']='PASS';s['free_bytes_after']=shutil.disk_usage(p).free;save(p/'ROOT.json',s);print('PASS '+str(p),flush=True)
except BaseException as exc:
 s['status']='FAILED';s['failure']=repr(exc);save(p/'ROOT.json',s);raise
