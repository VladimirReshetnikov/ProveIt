from pathlib import Path
import collections,gzip,hashlib,json,os,shutil,tempfile
P=Path(tempfile.mkdtemp(prefix='import-link-sharing-root-'))
prefixes=('arithmetic-pell-','arithmetic-negative-norms-','arithmetic-signed-pairs-','validator-seed-','control-frame215-','runtime215-','site215-','home215-','symbolic-core215-','register-boxes215-','machine-tape215-')
def need(c,m):
 if not c:raise RuntimeError(m)
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def save(p,x):
 with gzip.open(p,'wt')as f:json.dump(x,f,separators=(',',':'))
def terminal(p):
 for name in ['ROOT.json','AUTHOR.json','state.json']:
  q=p/name
  if q.is_file():
   try:
    if json.loads(q.read_text()).get('status')in['PASS','FAILED','POSTCHECK_FAILED']:return rec(q)
   except (ValueError,OSError):pass
 return None
before=shutil.disk_usage('/tmp').free;groups=collections.defaultdict(list);directories=[]
for p in Path('/tmp').iterdir():
 if not p.name.startswith(prefixes)or not p.is_dir()or not(p/'lib').is_dir():continue
 t=terminal(p)
 if t is None:continue
 directories.append(t)
 for q in(p/'lib').rglob('*'):
  if q.is_symlink():
   s=q.lstat();groups[(os.readlink(q),s.st_dev,s.st_uid,s.st_gid,s.st_mode)].append(dict(path=str(q),inode=s.st_ino,blocks=s.st_blocks))
plan=[]
for key,rows in groups.items():
 if len({x['inode']for x in rows})<=1:continue
 target,dev,uid,gid,mode=key
 plan.append(dict(target=target,device=dev,uid=uid,gid=gid,mode=mode,content=rec(rows[0]['path']),rows=rows))
save(P/'before.json.gz',dict(directories=directories,groups=plan,driver=rec(__file__),free_bytes=before))
changed=0
for group in plan:
 source=Path(group['rows'][0]['path']);ss=source.lstat();need(source.is_symlink()and os.readlink(source)==group['target'],'source link')
 for row in group['rows'][1:]:
  q=Path(row['path']);s=q.lstat();need(q.is_symlink()and os.readlink(q)==group['target'],'target link')
  need((s.st_dev,s.st_uid,s.st_gid,s.st_mode)==(group['device'],group['uid'],group['gid'],group['mode']),'metadata identity')
  if s.st_ino==ss.st_ino:continue
  tmp=q.with_name(q.name+'.share-link-root');need(not tmp.exists()and not tmp.is_symlink(),'fresh temporary link')
  os.link(source,tmp,follow_symlinks=False);need(tmp.is_symlink()and os.readlink(tmp)==group['target'],'new link identity')
  os.replace(tmp,q);need(q.is_symlink()and q.lstat().st_ino==ss.st_ino and os.readlink(q)==group['target'],'post replacement identity');changed+=1
 need(rec(source)['sha256']==group['content']['sha256'],'same provider bytes')
for t in directories:need(rec(t['path'])['sha256']==t['sha256'],'terminal state unchanged')
result=dict(status='PASS',private=str(P),driver=rec(__file__),plan=rec(P/'before.json.gz'),terminal_directories=len(directories),groups=len(plan),replaced_duplicate_links=changed,free_before=before,free_after=shutil.disk_usage('/tmp').free,qualification='Only identical terminal-overlay symlink inodes shared; every original link path/target and provider bytes retained. Regular outputs, source and evidence files untouched.')
(P/'result.json').write_text(json.dumps(result,indent=2)+'\n');shutil.copyfile(__file__,P/'driver.py');print(json.dumps(result,indent=2),flush=True)
