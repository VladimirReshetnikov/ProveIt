from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
REV=R/'Computability/DiophantineConsistency/reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(ok,s):
 if not ok:raise RuntimeError(s)
name=sys.argv[1];mode=sys.argv[2]
packet=REV/(name+('-dependency-replay.json'if mode=='ha'else'-replay.json'))
d=json.loads(packet.read_text());peer=Path(tempfile.mkdtemp(prefix=name+'-root-peer-'));lib=peer/'lib';lib.mkdir();pins=[]
if mode=='ha':
 modules=d['modules'];leaves=d['fresh_modules'];compiler=d['compiler']['path'];input_record=None
 require(sha(compiler)==d['compiler']['sha256'],'Compiler pin')
 for n,e in d['package_identity'].items():
  require(sha(R/n)==e['current_sha256'],'Current '+n)
  require(sha(Path('/home/codex/src/Proofs')/n)==e['cache_sha256'],'Cache '+n)
else:
 if mode=='natural':
  ip=REV/(name+'-author-replay/inputs.json');require(sha(ip)==d['inputs_sha256'],'Natural input pin');i=json.loads(ip.read_text());modules=i['modules'];leaves=d['results'];compiler=i['compiler'];input_record={'path':str(ip),'sha256':sha(ip)}
  for e in i['pins']:
   require(sha(e['path'])==e['sha256'],'Natural input '+e['path']);pins.append(e)
 else:
  i=d['inputs'];modules=i['modules'];leaves=d['final_leaves'];compiler=i['compiler'];input_record=None
  require(sha(compiler)==i['compiler_sha256'],'Compiler pin')
  require(sha(R/'lake-manifest.json')==i['manifest_sha256'],'Manifest pin')
  parents=i.get('parent_receipts',[i['parent_receipt']]if'parent_receipt'in i else[])
  for e in [*i['external'],*parents]:
   require(sha(e['path'])==e['sha256'],'External/prior pin '+e['path']);pins.append(e)
for e in modules:
 for field,key in [('source','source_sha256'),('cache_source','cache_source_sha256')]:
  if field not in e:continue
  p=R/Path(e[field]);require(sha(p)==e[key],'Source pin '+str(p));pins.append({'path':str(p),'sha256':e[key]})
 objects=e['objects']if'objects'in e else[{'path':e['object'],'sha256':e['object_sha256']}]
 for o in objects:
  require(sha(o['path'])==o['sha256'],'Object pin '+o['path']);pins.append(o)
  target=lib/Path(*e['module'].split('.')[:-1])/Path(o['path']).name;target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(o['path'])
for e in leaves:
 p=R/Path(e['source']);require(sha(p)==e['source_sha256'],'Fresh source pin')
 o=e['object']if isinstance(e['object'],dict)else{'path':e['object'],'sha256':e['object_sha256']}
 require(sha(o['path'])==o['sha256'],'Author fresh object');require(sha(e['log'])==e['log_sha256'],'Author log')
(peer/'pins.json').write_text(json.dumps(pins,indent=2)+'\n');(peer/'packet.json').write_text(json.dumps(d,indent=2)+'\n')
locations=Path('/tmp/root-frozen-leaf-replay-locations.json');ls=json.loads(locations.read_text())if locations.exists()else{};ls[name]=str(peer);locations.write_text(json.dumps(ls,indent=2)+'\n')
external=json.loads((REV/'current-positive-zero2011-refresh/manifest.json').read_text())['external_lean_path'];env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib),*external]);env.pop('LEAN_SRC_PATH',None)
s={'status':'RUNNING','name':name,'mode':mode,'packet_sha256':sha(packet),'driver_sha256':sha(__file__),'source_snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'prerequisite_count':len(modules),'prerequisite_pin_count':len(pins),'input_record':input_record,'completed':[]}
def save(): (peer/'state.json').write_text(json.dumps(s,indent=2)+'\n')
save()
try:
 for e in leaves:
  n=e['module'];n=n if'.'in n else'DiophantineConsistency.'+n;p=R/Path(e['source']);out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);log=peer/(n+'.txt');cmd=[compiler,'-M6000','-j1','-DElab.async=false','-o',str(out),str(p)];start=time.time()
  with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  x={'module':n,'command':cmd,'source':str(p),'source_sha256':sha(p),'exit_code':code,'seconds':time.time()-start,'log':str(log),'log_sha256':sha(log),'object':str(out),'object_sha256':sha(out)if code==0 else None};s['completed'].append(x);save();print(json.dumps(x),flush=True);require(code==0,'Lean failure '+n)
  reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())
  allowed={'propext','Quot.sound'}if mode in ['ha','natural']else{'propext','Quot.sound','Classical.choice'}
  for title,ax in reports:require(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<=allowed,'Extra axiom '+title)
  x['axiom_reports']=reports;expected=e['object']['sha256']if isinstance(e['object'],dict)else e['object_sha256'];x['matches_author']=x['object_sha256']==expected;save()
 for e in pins:require(sha(e['path'])==e['sha256'],'Postcheck '+e['path'])
 for e in leaves:require(sha(R/Path(e['source']))==e['source_sha256'],'Fresh source postcheck')
 s['status']='PASS';save();print(json.dumps({'status':'PASS','name':name,'private':str(peer),'prerequisite_count':len(modules),'reports':sum(len(e['axiom_reports'])for e in s['completed']),'all_objects_match_author':all(e['matches_author']for e in s['completed'])}),flush=True)
except BaseException as exc:
 s.update(status='FAILED',failure=str(exc));save();raise
