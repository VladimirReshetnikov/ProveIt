from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';mp=V/'fourteen-nonzero-spheres-replay.json';d=json.loads(mp.read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(e):assert sha(e['path'])==e['sha256'],e['path']
p=Path(tempfile.mkdtemp(prefix='fourteen-nonzero-root-peer-'));lib=p/'lib';lib.mkdir();pins=[dict(path=str(mp),sha256=sha(mp))]
g=d['generic']['inputs'];a=d['actual_carrier']['inputs'];compiler=g['compiler'];check(compiler);assert sha(R/'lake-manifest.json')==g['manifest_sha256']
for e in d['files']:check(e);pins.append(e)
for e in g['package_roots']:
 for k in ['source','object']:
  q=dict(path=e[k],sha256=e[k+'_sha256']);check(q);pins.append(q)
for k in ['parent_plan','parent_state','generic_input','generic_run']:check(a[k]);pins.append(a[k])
for e in a['selected_custom']:
 check(e['source']);check(e['object']);pins += [e['source'],e['object']]
 q=lib/Path(*e['module'].split('.')).with_suffix('.olean');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(e['object']['path'])
for e in a['companions']:check(e);pins.append(e)
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib),*g['LEAN_PATH'][1:]]);env.pop('LEAN_SRC_PATH',None)
leaves=d['generic']['run']+d['actual_carrier']['run'];s=dict(status='RUNNING',private=str(p),driver_sha256=sha(__file__),metadata_sha256=sha(mp),cached_custom_count=len(a['selected_custom']),pins=pins,completed=[])
def save():(p/'ROOT.json').write_text(json.dumps(s,indent=2)+'\n')
save();Path('/tmp/fourteen-nonzero-root-location.txt').write_text(str(p))
for e in leaves:
 assert shutil.disk_usage(p).free>=512*1024*1024
 src=Path(e['path']);assert sha(src)==e['sha256'];check(e['object']);n=e['module'];out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);log=p/(n+'.txt');cmd=[compiler['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];start=time.time()
 with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 x=dict(module=n,source=str(src),source_sha256=sha(src),command=cmd,exit_code=code,seconds=time.time()-start,log=str(log),log_sha256=sha(log),object=str(out),object_sha256=sha(out)if code==0 else None);s['completed'].append(x);save();print(json.dumps(x),flush=True);assert code==0,n
 reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());x['axiom_reports']=reports
 for title,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},title
 x['matches_author']=x['object_sha256']==e['object']['sha256'];save()
for e in pins:check(e)
for e in leaves:assert sha(e['path'])==e['sha256']
s['status']='PASS';save();print(json.dumps(dict(status='PASS',private=str(p),reports=sum(len(e['axiom_reports'])for e in s['completed']),all_objects_match_author=all(e['matches_author']for e in s['completed']))),flush=True)
