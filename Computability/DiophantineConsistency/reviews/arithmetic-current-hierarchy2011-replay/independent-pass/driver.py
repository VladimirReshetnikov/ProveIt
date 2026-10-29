from pathlib import Path
import json,hashlib,os,subprocess,tempfile,time,re,shutil
P=Path('/tmp/current-hierarchy2011-author-betz9tp8');s=json.loads((P/'AUTHOR.json').read_text());i=json.loads(Path(s['attempts'][-1]['inputs']['path']).read_text());assert json.loads((P/'postcheck.json').read_text())['status']=='PASS'
Q=Path(tempfile.mkdtemp(prefix='current-hierarchy2011-independent-')); L=Q/'lib';L.mkdir(); shutil.copyfile(__file__,Q/'driver.py')

for f in (P/'lib').rglob('*'):
 if f.is_file() and f.name not in ['ArithmeticCurrentHierarchy2011.olean','ArithmeticCurrentHierarchy2011Checks.olean']:
  dest=L/f.relative_to(P/'lib');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve())
paths=[str(L),*i['LEAN_PATH'][1:]];env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
rows=[]
for ar in s['records'][-2:]:
 n=ar['module']; src=Path(ar['snapshot']['path']); output=L/Path(*n.split('.')).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True);log=Q/(n+'.log');timing=Q/(n+'.time')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==ar['snapshot']['sha256']
 cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-R',str(P/'attempts/001/src'),'-o',str(output),str(src)];start=time.monotonic()
 with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],env=env,cwd='/home/codex/.codex/worktrees/46be/Proofs',stdout=f,stderr=subprocess.STDOUT).returncode
 def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
 row=dict(module=n,code=code,seconds=time.monotonic()-start,command=cmd,object_sha=sha(output) if output.exists() else None,log_sha=sha(log),author_object_sha=ar['objects'][0]['sha256'],author_log_sha=ar['log']['sha256']);rows.append(row);print(json.dumps(row),flush=True)
 assert code==0 and row['object_sha']==row['author_object_sha'] and row['log_sha']==row['author_log_sha']
(Q/'result.json').write_text(json.dumps({'status':'PASS','provider':str(L),'records':rows,'parent_postcheck_sha':sha(P/'postcheck.json')},indent=2)+'\n');print('PASS',Q,flush=True)
