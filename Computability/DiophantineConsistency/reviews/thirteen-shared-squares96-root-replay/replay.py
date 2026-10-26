from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=R/'Computability/DiophantineConsistency';D=B/'reviews/thirteen-shared-squares96-replay';p=Path(tempfile.mkdtemp(prefix='thirteen-shared96-root-peer-'));lib=p/'lib';lib.mkdir();pins=[]
def sha(q):return hashlib.sha256(Path(q).read_bytes()).hexdigest()
def pin(q,s):assert sha(q)==s,str(q);pins.append({'path':str(q),'sha256':s})
d=json.loads((D/'REPLAY.json').read_text());i=json.loads((D/'inputs.json').read_text());pr=json.loads((D/'prerequisites.json').read_text());pin(D/'prerequisites.json',i['prerequisites_sha256']);pin(i['compiler']['path'],i['compiler']['sha256'])
for e in d['durable_logs_and_inventory']+d['source_artifacts']:pin(B/e['path'],e['sha256'])
for e in pr['inventory']:
 for k in ['source','object']:pin(e[k]['path'],e[k]['sha256'])
for e in pr['parent_fresh']:
 pin(B/'Lean/DiophantineConsistency'/(e['module']+'.lean'),e['source_sha256']);pin(e['object'],e['object_sha256'])
pin(pr['parent_receipt']['path'],pr['parent_receipt']['sha256'])
for e in pr['available_links']:
 pin(e['object'],e['sha256']);q=lib/Path(*e['module'].split('.')).with_suffix('.olean');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(e['object'])
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib),*i['LEAN_PATH'][1:]]);env.pop('LEAN_SRC_PATH',None)
s={'scope':'Two fresh leaves over447 pinned source/object pairs plus2 fresh accepted parent leaves; external packages cached.','private':str(p),'pins':pins,'prerequisite_count':len(pr['inventory'])+len(pr['parent_fresh']),'lean_path':env['LEAN_PATH'],'driver_sha256':sha(__file__),'completed':[],'status':'RUNNING'}
def save():(p/'ROOT.json').write_text(json.dumps(s,indent=2)+'\n')
(p/'packet.json').write_bytes((D/'REPLAY.json').read_bytes());save();Path('/tmp/shared96-root-location.txt').write_text(str(p))
for e in d['fresh']:
 assert shutil.disk_usage(p).free>=512*1024*1024
 src=Path(e['source']);pin(src,e['source_sha256']);pin(e['object'],e['object_sha256']);name=e['module'];out=lib/'DiophantineConsistency'/(name+'.olean');out.parent.mkdir(parents=True,exist_ok=True);log=p/(name+'.txt');cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];start=time.time()
 with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 x={'module':name,'command':cmd,'exit_code':code,'seconds':time.time()-start,'source':str(src),'source_sha256':sha(src),'log':str(log),'log_sha256':sha(log),'object':str(out),'object_sha256':sha(out)if code==0 else None};s['completed'].append(x);save();print(json.dumps(x),flush=True);assert code==0,name
 reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());x['axiom_reports']=reports
 for title,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},title
 x['matches_author']=x['object_sha256']==e['object_sha256'];save()
for e in pins:assert sha(e['path'])==e['sha256'],e['path']
s['status']='PASS';save();print(json.dumps({'status':'PASS','private':str(p),'reports':sum(len(e['axiom_reports'])for e in s['completed']),'all_objects_match_author':all(e['matches_author']for e in s['completed'])}),flush=True)
